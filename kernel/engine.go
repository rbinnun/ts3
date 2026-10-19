package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/google/mangle/analysis"
	"github.com/google/mangle/ast"
	"github.com/google/mangle/engine"
	"github.com/google/mangle/factstore"
	"github.com/google/mangle/parse"
	_ "modernc.org/sqlite"
)

const (
	engineFile        = "kernel/engine.go"
	toolsFile         = "kernel/tools.go"
	derivedOrigin     = "derived"
	theKnowledge      = "the knowledge"
	theFolder         = "the folder"
	theCertificate    = "the certificate"
	brokenAnswer      = "broken"
	provenAnswer      = "true"
	changeArgument    = "change"
	plainLoader       = "rules and facts"
	rowsLoader        = "a row per line after the first with a cell for each column the first line names"
	ruleRows          = "every rule"
	factRows          = "every fact"
	derivationRows    = "every way a rule derives a fact"
	reasonRows        = "every reason of every derivation"
	certificateRows   = "every part the certificate holds"
	levelNamePart     = "the name of the level being proven"
	loadedHashPart    = "the hash of every file engine.go loads or the level is tested with"
	machineHashPart   = "the hash of every file that is part of the machine"
	answerPart        = "the answer"
	partContent       = "what the certificate holds"
	subjectContent    = "the file a hash is of and empty otherwise"
	valueContent      = "the sha256 of the file in hex or the level name or the answer"
	derivationIDValue = "the derivation id"
)

var computations = map[string]string{
	"a rule id":                     "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":                     "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a derivation id":               "the first 16 hex digits of the sha256 of the fact and the rule name and the reasons as plain lines joined by newlines",
	"a row name":                    "the file name and a colon and the line number",
	"a cell value":                  "the cell text read as a plain value",
	"a quoted value":                "a value between double quotes unless it holds a double quote and no single quote and then between single quotes",
	"a quote inside a quoted value": "the quote the value is between written twice",
	"a missing fact":                "a fact a level expects that the knowledge does not hold without the facts about what is missing or present",
	"a present fact":                "a fact a level rules out that the knowledge holds without the facts about what is missing or present",
	"an agent file":                 "agent.plain in a level folder which an agent writes and may rewrite on any run",
	"a level":                       "a folder next to the kernel folder named by the folder name",
	"the level being proven":        "the level whose folder runme.sh is run in",
	"a level file":                  "human.plain or agent.plain in the level folder",
	"a level store":                 "the level name followed by .db in the folder that holds the level folders",
	"a loaded level":                "the level being proven and every level a loaded level builds on where a level with no folder loads nothing",
	"a loaded file":                 "a level file of a loaded level and every file a level file says engine.go loads",
	"a tested file":                 "a file the level being proven is tested with found in its folder and loaded like a file engine.go loads",
	"a file name":                   "the path of the file from the folder that holds the level folders",
	"a proven level":                "a loaded level other than the level being proven whose store holds a certificate with the answer true and with the hash of every file it names as that file is now",
	"a certified file":              "a file loaded from the folder of a proven level",
	"a private fact":                "a fact of a private fact pattern which engine.go does not load from a certified file",
}

var selfDescriptions = map[string]bool{
	"engine.go, prints, the knowledge":               true,
	"engine.go, prints in, plain language":           true,
	"engine.go, prints to, standard output":          true,
	"the knowledge, is published to, the store":      true,
	"the store, is the sqlite file, the level store": true,
}

var describedPredicates = []predicate{
	{"prints", 2}, {"prints in", 2}, {"prints to", 2}, {"is published to", 2}, {"is the sqlite file", 2},
}

var rowContents = map[string][]string{
	ruleRows:        {"the rule id", "the rule name", "the file the rule is in", "the number of the line the rule starts on", "the rule lines joined by newlines"},
	factRows:        {"the fact id", "the fact as one plain line", "the go file that observed the fact and derived for every other fact"},
	derivationRows:  {derivationIDValue, "the fact id", "the rule name"},
	reasonRows:      {derivationIDValue, "the number of the condition in the rule", "the condition with its blanks filled as one plain line"},
	certificateRows: {partContent, subjectContent, valueContent},
}

var certificateParts = map[string]bool{levelNamePart: true, loadedHashPart: true, machineHashPart: true, answerPart: true}

var mangleKeywords = map[string]bool{"do": true, "let": true, "bound": true, "descr": true, "inclusion": true}

var (
	blankPattern  = regexp.MustCompile(`^\[([^\[\]]*)\]$`)
	numberPattern = regexp.MustCompile(`^-?[0-9]+$`)
	namePattern   = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	sqlName       = regexp.MustCompile(`^[a-z_][a-z0-9_]*$`)
)

type termKind int

const (
	textTerm termKind = iota
	numberTerm
	blankTerm
)

type term struct {
	kind   termKind
	text   string
	number int64
}

func textOf(s string) term     { return term{kind: textTerm, text: s} }
func numberOf(n int64) term    { return term{kind: numberTerm, number: n} }
func blankOf(name string) term { return term{kind: blankTerm, text: name} }

func (t term) plain() string {
	if t.kind == numberTerm {
		return strconv.FormatInt(t.number, 10)
	}
	return t.text
}

type predicate struct {
	name  string
	arity int
}

type atom struct {
	name string
	args []term
}

func (a atom) predicate() predicate { return predicate{a.name, len(a.args)} }

func (a atom) line() string { return renderAtom(a, false) }

type builtin struct {
	arity     int
	format    string
	assigning bool
}

var builtins = map[string]builtin{
	"ends with":            {2, ":string:ends_with(%[1]s, %[2]s)", false},
	"starts with":          {2, ":string:starts_with(%[1]s, %[2]s)", false},
	"differs from":         {2, "%[1]s != %[2]s", false},
	"is before":            {2, ":lt(%[1]s, %[2]s)", false},
	"is the difference of": {3, "%[1]s = fn:minus(%[2]s, %[3]s)", true},
	"is at most":           {2, ":le(%[1]s, %[2]s)", false},
	"is one more than":     {2, "%[1]s = fn:plus(%[2]s, 1)", true},
	"is the join of":       {3, "%[1]s = fn:string:concat(%[2]s, %[3]s)", true},
}

func (a atom) builtin() (builtin, bool) {
	b, ok := builtins[a.name]
	return b, ok && len(a.args) == b.arity
}

type condition struct {
	negated bool
	atom    atom
}

func (c condition) line() string {
	if c.negated {
		return "not " + renderAtom(c.atom, true)
	}
	return renderAtom(c.atom, true)
}

type rule struct {
	file       string
	line       int
	lines      []string
	head       atom
	conditions []condition
}

func (r *rule) name() string { return fmt.Sprintf("%s:%d", r.file, r.line) }

func (r *rule) text() string { return strings.Join(r.lines, "\n") }

func (r *rule) id() string { return shortHash(r.text()) }

func (r *rule) readBack() string {
	lines := []string{renderAtom(r.head, false)}
	for i, c := range r.conditions {
		word := "and"
		if i == 0 {
			word = "if"
		}
		lines = append(lines, "    "+word+" "+c.line())
	}
	return strings.Join(lines, "\n")
}

func (r *rule) atoms() []atom {
	atoms := []atom{r.head}
	for _, c := range r.conditions {
		atoms = append(atoms, c.atom)
	}
	return atoms
}

func shortHash(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])[:16]
}

func fileHash(name string) string {
	content, err := os.ReadFile(name)
	if err != nil {
		return ""
	}
	sum := sha256.Sum256(content)
	return hex.EncodeToString(sum[:])
}

type element struct {
	value  string
	quoted bool
}

func splitElements(line string) ([]element, error) {
	var elements []element
	i := 0
	for {
		for i < len(line) && line[i] == ' ' {
			i++
		}
		if i < len(line) && (line[i] == '"' || line[i] == '\'') {
			quote := line[i]
			var value strings.Builder
			j := i + 1
			closed := false
			for j < len(line) {
				if line[j] == quote {
					if j+1 < len(line) && line[j+1] == quote {
						value.WriteByte(quote)
						j += 2
						continue
					}
					closed = true
					j++
					break
				}
				value.WriteByte(line[j])
				j++
			}
			if !closed {
				return nil, errors.New("a quote is never closed")
			}
			elements = append(elements, element{value.String(), true})
			for j < len(line) && line[j] == ' ' {
				j++
			}
			if j == len(line) {
				return elements, nil
			}
			if line[j] != ',' {
				return nil, fmt.Errorf("a quoted value is followed by %s", line[j:])
			}
			i = j + 1
			continue
		}
		end := strings.IndexByte(line[i:], ',')
		if end < 0 {
			value := strings.TrimSpace(line[i:])
			if value == "" {
				return nil, errors.New("a part is empty")
			}
			return append(elements, element{value, false}), nil
		}
		value := strings.TrimSpace(line[i : i+end])
		if value == "" {
			return nil, errors.New("a part is empty")
		}
		elements = append(elements, element{value, false})
		i += end + 1
	}
}

func termOf(e element, blanks bool) (term, error) {
	if e.quoted {
		return textOf(e.value), nil
	}
	if match := blankPattern.FindStringSubmatch(e.value); match != nil {
		if !blanks {
			return term{}, fmt.Errorf("%s is a blank where no blank can be", e.value)
		}
		if !namePattern.MatchString(match[1]) {
			return term{}, fmt.Errorf("%s is not a blank name", e.value)
		}
		return blankOf(match[1]), nil
	}
	if numberPattern.MatchString(e.value) {
		if n, err := strconv.ParseInt(e.value, 10, 64); err == nil {
			return numberOf(n), nil
		}
	}
	return textOf(e.value), nil
}

func plainValue(text string) term {
	text = strings.TrimSpace(text)
	if elements, err := splitElements(text); err == nil && len(elements) == 1 && elements[0].quoted {
		return textOf(elements[0].value)
	}
	if t, err := termOf(element{text, false}, false); err == nil {
		return t
	}
	return textOf(text)
}

func isName(e element, t term) bool {
	return !e.quoted && t.kind == textTerm && namePattern.MatchString(t.text)
}

func makeAtom(elements []element, blanks, builtinsAllowed bool) (atom, error) {
	terms := make([]term, len(elements))
	for i, e := range elements {
		t, err := termOf(e, blanks)
		if err != nil {
			return atom{}, err
		}
		terms[i] = t
	}
	switch len(elements) {
	case 1:
		if !isName(elements[0], terms[0]) {
			return atom{}, fmt.Errorf("%s is not a sentence", elements[0].value)
		}
		return atom{name: terms[0].text}, nil
	case 2:
		return atom{}, errors.New("a statement has one part or at least three, not two")
	}
	if !isName(elements[1], terms[1]) {
		return atom{}, fmt.Errorf("%s is not a verb", elements[1].value)
	}
	if terms[1].text == "is" {
		if len(elements) != 3 || !isName(elements[2], terms[2]) {
			return atom{}, errors.New("is takes one subject and one name")
		}
		return atom{name: terms[2].text, args: []term{terms[0]}}, nil
	}
	args := append([]term{terms[0]}, terms[2:]...)
	a := atom{name: terms[1].text, args: args}
	if _, ok := a.builtin(); ok && !builtinsAllowed {
		return atom{}, fmt.Errorf("%s can only be a condition", a.name)
	}
	return a, nil
}

func parseLine(line string, blanks, builtinsAllowed bool) (atom, error) {
	elements, err := splitElements(line)
	if err != nil {
		return atom{}, err
	}
	return makeAtom(elements, blanks, builtinsAllowed)
}

func parseFact(line string) (atom, error) { return parseLine(line, false, false) }

func parsePattern(s string) (atom, error) {
	if strings.Contains(s, ",") {
		return parseLine(s, true, true)
	}
	var tokens []term
	rest := s
	for rest != "" {
		open := strings.IndexByte(rest, '[')
		if open < 0 {
			if words := strings.TrimSpace(rest); words != "" {
				tokens = append(tokens, textOf(words))
			}
			break
		}
		if words := strings.TrimSpace(rest[:open]); words != "" {
			tokens = append(tokens, textOf(words))
		}
		end := strings.IndexByte(rest[open:], ']')
		if end < 0 {
			return atom{}, fmt.Errorf("%s has a blank that is never closed", s)
		}
		name := rest[open+1 : open+end]
		if !namePattern.MatchString(name) {
			return atom{}, fmt.Errorf("%s has the blank [%s] which is not a blank name", s, name)
		}
		tokens = append(tokens, blankOf(name))
		rest = rest[open+end+1:]
	}
	if len(tokens) == 1 && tokens[0].kind == textTerm && namePattern.MatchString(tokens[0].text) {
		return atom{name: tokens[0].text}, nil
	}
	if len(tokens) < 2 || tokens[0].kind != blankTerm || tokens[1].kind != textTerm || !namePattern.MatchString(tokens[1].text) {
		return atom{}, fmt.Errorf("%s is not a fact pattern", s)
	}
	for _, t := range tokens[2:] {
		if t.kind != blankTerm {
			return atom{}, fmt.Errorf("%s is not a fact pattern", s)
		}
	}
	verb := tokens[1].text
	if len(tokens) == 2 {
		if !strings.HasPrefix(verb, "is ") {
			return atom{}, fmt.Errorf("%s is not a fact pattern", s)
		}
		return atom{name: strings.TrimPrefix(verb, "is "), args: []term{tokens[0]}}, nil
	}
	return atom{name: verb, args: append([]term{tokens[0]}, tokens[2:]...)}, nil
}

func needsQuotes(s string, leading bool) bool {
	return s == "" ||
		strings.ContainsAny(s, ",\n\r") ||
		s != strings.TrimSpace(s) ||
		s[0] == '"' || s[0] == '\'' ||
		numberPattern.MatchString(s) ||
		blankPattern.MatchString(s) ||
		(leading && strings.HasPrefix(s, "not "))
}

func quoteValue(s string) string {
	quote := `"`
	if strings.Contains(s, `"`) && !strings.Contains(s, "'") {
		quote = "'"
	}
	return quote + strings.ReplaceAll(s, quote, quote+quote) + quote
}

func renderTerm(t term, leading bool) string {
	switch t.kind {
	case numberTerm:
		return strconv.FormatInt(t.number, 10)
	case blankTerm:
		return "[" + t.text + "]"
	}
	if needsQuotes(t.text, leading) {
		return quoteValue(t.text)
	}
	return t.text
}

func renderAtom(a atom, leading bool) string {
	switch len(a.args) {
	case 0:
		return a.name
	case 1:
		return renderTerm(a.args[0], leading) + ", is, " + a.name
	}
	parts := []string{renderTerm(a.args[0], leading), a.name}
	for _, t := range a.args[1:] {
		parts = append(parts, renderTerm(t, false))
	}
	return strings.Join(parts, ", ")
}

func conditionBody(line string) (string, bool) {
	for _, prefix := range []string{"    if ", "    and "} {
		if strings.HasPrefix(line, prefix) {
			return line[len(prefix):], true
		}
	}
	return "", false
}

func parsePlain(file string, content string) ([]*rule, []string) {
	var rules []*rule
	var problems []string
	var current *rule
	if content == "" {
		return nil, nil
	}
	for i, line := range strings.Split(strings.TrimSuffix(content, "\n"), "\n") {
		where := fmt.Sprintf("%s:%d", file, i+1)
		if strings.TrimSpace(line) == "" {
			current = nil
			continue
		}
		if body, ok := conditionBody(line); ok {
			if current == nil {
				problems = append(problems, where+": a condition has no statement above it")
				continue
			}
			negated := strings.HasPrefix(body, "not ")
			if negated {
				body = body[len("not "):]
			}
			a, err := parseLine(body, true, true)
			if err != nil {
				problems = append(problems, where+": "+err.Error())
				continue
			}
			current.conditions = append(current.conditions, condition{negated, a})
			current.lines = append(current.lines, line)
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			problems = append(problems, where+": an indented line must start with if or and")
			current = nil
			continue
		}
		a, err := parseLine(line, true, false)
		if err != nil {
			problems = append(problems, where+": "+err.Error())
			current = nil
			continue
		}
		current = &rule{file: file, line: i + 1, lines: []string{line}, head: a}
		rules = append(rules, current)
	}
	return rules, problems
}

func mangleName(name string) string { return strings.ReplaceAll(name, " ", "_") }

func mangleVariable(name string) string {
	words := strings.Fields(name)
	for i, w := range words {
		words[i] = strings.ToUpper(w[:1]) + w[1:]
	}
	return strings.Join(words, "")
}

func mangleString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch {
		case r == '\\':
			b.WriteString(`\\`)
		case r == '"':
			b.WriteString(`\"`)
		case r == '\n':
			b.WriteString(`\n`)
		case r == '\t':
			b.WriteString(`\t`)
		case r < 0x20:
			fmt.Fprintf(&b, `\x%02x`, r)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func mangleTerm(t term, hidden map[string]bool) string {
	switch t.kind {
	case numberTerm:
		return strconv.FormatInt(t.number, 10)
	case blankTerm:
		if hidden[t.text] {
			return "_"
		}
		return mangleVariable(t.text)
	}
	return mangleString(t.text)
}

func mangleAtom(a atom, hidden map[string]bool) string {
	args := make([]any, len(a.args))
	texts := make([]string, len(a.args))
	for i, t := range a.args {
		texts[i] = mangleTerm(t, hidden)
		args[i] = texts[i]
	}
	if b, ok := a.builtin(); ok {
		return fmt.Sprintf(b.format, args...)
	}
	return mangleName(a.name) + "(" + strings.Join(texts, ", ") + ")"
}

func mangleLine(line string) (string, error) {
	a, err := parseLine(line, true, true)
	if err != nil {
		return "", err
	}
	if _, ok := a.builtin(); ok {
		return mangleAtom(a, nil), nil
	}
	return mangleAtom(a, nil) + ".", nil
}

func blankUses(r *rule) map[string]int {
	uses := map[string]int{}
	for _, a := range r.atoms() {
		for _, t := range a.args {
			if t.kind == blankTerm {
				uses[t.text]++
			}
		}
	}
	return uses
}

func hiddenBlanks(r *rule) map[string]bool {
	uses := blankUses(r)
	hidden := map[string]bool{}
	for _, c := range r.conditions {
		if !c.negated {
			continue
		}
		for _, t := range c.atom.args {
			if t.kind == blankTerm && uses[t.text] == 1 {
				hidden[t.text] = true
			}
		}
	}
	return hidden
}

func ruleBlanks(r *rule, hidden map[string]bool) []string {
	var names []string
	seen := map[string]bool{}
	for _, a := range r.atoms() {
		for _, t := range a.args {
			if t.kind == blankTerm && !hidden[t.text] && !seen[t.text] {
				seen[t.text] = true
				names = append(names, t.text)
			}
		}
	}
	return names
}

func mangleBody(r *rule, hidden map[string]bool) string {
	parts := make([]string, len(r.conditions))
	for i, c := range r.conditions {
		parts[i] = mangleAtom(c.atom, hidden)
		if c.negated {
			parts[i] = "!" + parts[i]
		}
	}
	return strings.Join(parts, ", ")
}

func mangleRule(r *rule) string {
	head := mangleAtom(r.head, nil)
	if len(r.conditions) == 0 {
		return head + "."
	}
	return head + " :- " + mangleBody(r, hiddenBlanks(r)) + "."
}

func derivationName(index int) string { return fmt.Sprintf("derivation__%d", index) }

func derivationRule(index int, r *rule) string {
	hidden := hiddenBlanks(r)
	names := ruleBlanks(r, hidden)
	variables := make([]string, len(names))
	for i, name := range names {
		variables[i] = mangleVariable(name)
	}
	return derivationName(index) + "(" + strings.Join(variables, ", ") + ") :- " + mangleBody(r, hidden) + "."
}

func ruleProblems(r *rule) []string {
	var problems []string
	hidden := hiddenBlanks(r)
	bound := map[string]bool{}
	reported := map[string]bool{}
	need := func(t term) {
		if t.kind == blankTerm && !hidden[t.text] && !bound[t.text] && !reported[t.text] {
			reported[t.text] = true
			problems = append(problems, fmt.Sprintf("%s leaves [%s] open", r.name(), t.text))
		}
	}
	for _, c := range r.conditions {
		b, isBuiltin := c.atom.builtin()
		if c.negated {
			if isBuiltin {
				problems = append(problems, fmt.Sprintf("%s cannot say not before %s", r.name(), c.atom.name))
			}
			continue
		}
		if isBuiltin {
			first := 0
			if b.assigning {
				first = 1
			}
			for _, t := range c.atom.args[first:] {
				need(t)
			}
			if b.assigning && c.atom.args[0].kind == blankTerm {
				bound[c.atom.args[0].text] = true
			}
			continue
		}
		for _, t := range c.atom.args {
			if t.kind == blankTerm {
				bound[t.text] = true
			}
		}
	}
	for _, c := range r.conditions {
		if c.negated {
			for _, t := range c.atom.args {
				need(t)
			}
		}
	}
	for _, t := range r.head.args {
		need(t)
	}
	return problems
}

func toMangle(a atom) ast.Atom {
	args := make([]ast.BaseTerm, len(a.args))
	for i, t := range a.args {
		if t.kind == numberTerm {
			args[i] = ast.Number(t.number)
		} else {
			args[i] = ast.String(t.text)
		}
	}
	return ast.Atom{Predicate: ast.PredicateSym{Symbol: mangleName(a.name), Arity: len(a.args)}, Args: args}
}

func fromMangle(t ast.BaseTerm) term {
	c, ok := t.(ast.Constant)
	if !ok {
		return textOf(t.String())
	}
	if n, err := c.NumberValue(); err == nil {
		return numberOf(n)
	}
	if s, err := c.StringValue(); err == nil {
		return textOf(s)
	}
	return textOf(c.String())
}

func substitute(a atom, binding map[string]term) atom {
	args := make([]term, len(a.args))
	for i, t := range a.args {
		args[i] = t
		if t.kind == blankTerm {
			if value, ok := binding[t.text]; ok {
				args[i] = value
			}
		}
	}
	return atom{name: a.name, args: args}
}

type derivation struct {
	fact    atom
	rule    *rule
	reasons []condition
}

func (d derivation) lines() []string {
	lines := []string{d.fact.line(), d.rule.name()}
	for _, reason := range d.reasons {
		lines = append(lines, reason.line())
	}
	return lines
}

func (d derivation) id() string { return shortHash(strings.Join(d.lines(), "\n")) }

type knowledge struct {
	facts       map[string]atom
	byPredicate map[predicate][]atom
	derivations []derivation
}

func newKnowledge() *knowledge {
	return &knowledge{facts: map[string]atom{}, byPredicate: map[predicate][]atom{}}
}

func (k *knowledge) add(a atom) {
	key := a.line()
	if _, ok := k.facts[key]; ok {
		return
	}
	k.facts[key] = a
	k.byPredicate[a.predicate()] = append(k.byPredicate[a.predicate()], a)
}

func (k *knowledge) has(a atom) bool {
	_, ok := k.facts[a.line()]
	return ok
}

func sortAtoms(atoms []atom) []atom {
	sorted := append([]atom{}, atoms...)
	sort.Slice(sorted, func(i, j int) bool { return sorted[i].line() < sorted[j].line() })
	return sorted
}

func (k *knowledge) all(name string, arity int) []atom {
	return sortAtoms(k.byPredicate[predicate{name, arity}])
}

func (k *knowledge) lines() []string {
	lines := make([]string, 0, len(k.facts))
	for line := range k.facts {
		lines = append(lines, line)
	}
	sort.Strings(lines)
	return lines
}

type factSource func(name string, arity int) []atom

func valueOf(facts factSource, name, subject string) string {
	for _, a := range facts(name, 2) {
		if a.args[0].plain() == subject {
			return a.args[1].plain()
		}
	}
	return ""
}

type loadedFile struct {
	name  string
	level string
	rules []*rule
}

type session struct {
	root       string
	level      string
	levelDir   string
	change     bool
	files      []*loadedFile
	loaded     []string
	tested     []string
	rules      []*rule
	observed   []atom
	origins    map[string]string
	problems   []string
	problemSet map[string]bool
	called     map[string]bool
	programs   map[bool]*analysis.ProgramInfo
	mutex      sync.Mutex
}

func newSession(arguments []string) (*session, error) {
	directory, err := os.Getwd()
	if err != nil {
		return nil, err
	}
	return &session{
		root:       filepath.Dir(directory),
		level:      filepath.Base(directory),
		levelDir:   directory,
		change:     len(arguments) > 0 && arguments[0] == changeArgument,
		origins:    map[string]string{},
		problemSet: map[string]bool{},
		called:     map[string]bool{},
		programs:   map[bool]*analysis.ProgramInfo{},
	}, nil
}

func (s *session) problem(text string) {
	s.mutex.Lock()
	defer s.mutex.Unlock()
	if !s.problemSet[text] {
		s.problemSet[text] = true
		s.problems = append(s.problems, text)
	}
}

func (s *session) observe(a atom, origin string) {
	key := a.line()
	if _, ok := s.origins[key]; ok {
		return
	}
	s.origins[key] = origin
	s.observed = append(s.observed, a)
}

func (s *session) path(name string) string {
	return filepath.Join(s.root, filepath.FromSlash(name))
}

func fileName(name string) (string, bool) {
	clean := path.Clean(name)
	if name == "" || path.IsAbs(clean) || clean == "." || clean == ".." || strings.HasPrefix(clean, "../") {
		return "", false
	}
	return clean, true
}

func levelOf(name string) string {
	if i := strings.IndexByte(name, '/'); i >= 0 {
		return name[:i]
	}
	return ""
}

func (s *session) stated(name string, arity int) []atom {
	var found []atom
	for _, f := range s.files {
		for _, r := range f.rules {
			if len(r.conditions) > 0 || r.head.name != name || len(r.head.args) != arity {
				continue
			}
			ground := true
			for _, t := range r.head.args {
				if t.kind == blankTerm {
					ground = false
				}
			}
			if ground {
				found = append(found, r.head)
			}
		}
	}
	return found
}

func (s *session) addPlain(name, level string, content []byte) {
	rules, problems := parsePlain(name, string(content))
	for _, p := range problems {
		s.problem(p)
	}
	s.files = append(s.files, &loadedFile{name: name, level: level, rules: rules})
}

func (s *session) addRows(name string, content []byte) {
	reader := csv.NewReader(bytes.NewReader(content))
	reader.FieldsPerRecord = -1
	header, err := reader.Read()
	if err == io.EOF {
		return
	}
	if err != nil {
		s.problem(fmt.Sprintf("%s cannot be read as rows: %v", name, err))
		return
	}
	for {
		record, err := reader.Read()
		if err == io.EOF {
			return
		}
		if err != nil {
			s.problem(fmt.Sprintf("%s cannot be read as rows: %v", name, err))
			return
		}
		number, _ := reader.FieldPos(0)
		row := textOf(fmt.Sprintf("%s:%d", name, number))
		s.observe(atom{name: "is a row of", args: []term{row, textOf(name)}}, engineFile)
		s.observe(atom{name: "is on line", args: []term{row, numberOf(int64(number))}}, engineFile)
		for i, cell := range record {
			if i < len(header) {
				s.observe(atom{name: "has the cell", args: []term{row, textOf(header[i]), plainValue(cell)}}, engineFile)
			}
		}
	}
}

func (s *session) kindOf(name string) string {
	kind, longest := "", -1
	for _, a := range s.stated("means", 2) {
		ending := a.args[0].plain()
		if strings.HasSuffix(name, ending) && len(ending) > longest {
			kind, longest = a.args[1].plain(), len(ending)
		}
	}
	return kind
}

func (s *session) loadByKind(name string) {
	content, err := os.ReadFile(s.path(name))
	if err != nil {
		return
	}
	kind := s.kindOf(name)
	switch valueOf(s.stated, "is loaded as", kind) {
	case plainLoader:
		s.addPlain(name, levelOf(name), content)
	case rowsLoader:
		s.addRows(name, content)
	default:
		s.problem(fmt.Sprintf("%s cannot be loaded because nothing says how %s is loaded", name, kind))
	}
}

func (s *session) loadLevel(level string, seen map[string]bool) {
	if level == "" || strings.ContainsAny(level, `/\`) || level == "." || level == ".." {
		return
	}
	for _, base := range []string{"human.plain", "agent.plain"} {
		name := level + "/" + base
		if seen[name] {
			continue
		}
		content, err := os.ReadFile(s.path(name))
		if err != nil {
			continue
		}
		seen[name] = true
		s.loaded = append(s.loaded, name)
		s.addPlain(name, level, content)
	}
}

func (s *session) load() {
	seen := map[string]bool{}
	levels := map[string]bool{s.level: true}
	order := []string{s.level}
	s.loadLevel(s.level, seen)
	for grown := true; grown; {
		grown = false
		for _, a := range s.stated("builds on", 2) {
			if !levels[a.args[0].plain()] || levels[a.args[1].plain()] {
				continue
			}
			other := a.args[1].plain()
			levels[other] = true
			order = append(order, other)
			s.loadLevel(other, seen)
			grown = true
		}
	}
	for _, a := range s.stated("loads", 2) {
		if a.args[0].plain() != engineFile {
			continue
		}
		name, ok := fileName(a.args[1].plain())
		if !ok {
			s.problem(fmt.Sprintf("%s is not a file name", a.args[1].plain()))
			continue
		}
		if seen[name] {
			continue
		}
		seen[name] = true
		if _, err := os.Stat(s.path(name)); err != nil {
			continue
		}
		s.loaded = append(s.loaded, name)
		s.loadByKind(name)
	}
	proven := map[string]bool{}
	for _, level := range order[1:] {
		if s.storeProves(level) {
			proven[level] = true
			s.observe(atom{name: "proven", args: []term{textOf(level)}}, engineFile)
		}
	}
	private := map[predicate]bool{}
	for _, a := range s.stated("private to its level", 1) {
		if p, err := parsePattern(a.args[0].plain()); err == nil {
			private[p.predicate()] = true
		} else {
			s.problem(err.Error())
		}
	}
	for _, f := range s.files {
		if !proven[levelOf(f.name)] {
			continue
		}
		s.observe(atom{name: "certified", args: []term{textOf(f.name)}}, engineFile)
		var kept []*rule
		for _, r := range f.rules {
			if len(r.conditions) == 0 && private[r.head.predicate()] {
				continue
			}
			kept = append(kept, r)
		}
		f.rules = kept
	}
	for _, a := range s.stated("is tested with", 2) {
		if a.args[0].plain() != s.level {
			continue
		}
		name, ok := fileName(a.args[1].plain())
		if !ok || levelOf(name) != s.level || seen[name] {
			continue
		}
		if _, err := os.Stat(s.path(name)); err != nil {
			continue
		}
		seen[name] = true
		s.tested = append(s.tested, name)
		s.loadByKind(name)
	}
	for _, f := range s.files {
		s.rules = append(s.rules, f.rules...)
	}
}

func certificateTable(facts factSource) (table, bool) {
	tables, problems := schema(facts)
	if len(problems) > 0 {
		return table{}, false
	}
	for _, t := range tables {
		if t.source == certificateRows {
			return t, true
		}
	}
	return table{}, false
}

func (s *session) storeProves(level string) bool {
	target := filepath.Join(s.root, level+".db")
	if _, err := os.Stat(target); err != nil {
		return false
	}
	certificate, ok := certificateTable(s.stated)
	if !ok {
		return false
	}
	columns := map[string]string{}
	for _, c := range certificate.columns {
		columns[c.content] = c.name
	}
	part, subject, value := columns[partContent], columns[subjectContent], columns[valueContent]
	if part == "" || subject == "" || value == "" {
		return false
	}
	db, err := sql.Open("sqlite", target)
	if err != nil {
		return false
	}
	defer db.Close()
	rows, err := db.Query(fmt.Sprintf(`SELECT "%s", "%s", "%s" FROM "%s"`, part, subject, value, certificate.name))
	if err != nil {
		return false
	}
	defer rows.Close()
	answered := false
	for rows.Next() {
		var named, file, held string
		if err := rows.Scan(&named, &file, &held); err != nil {
			return false
		}
		if named == answerPart {
			if held != provenAnswer {
				return false
			}
			answered = true
		}
		if file != "" && fileHash(s.path(file)) != held {
			return false
		}
	}
	return answered && rows.Err() == nil
}

func (s *session) observeRules() {
	positions := map[predicate]map[int]bool{}
	arities := map[string]int{}
	for _, r := range s.rules {
		for _, a := range r.atoms() {
			if _, ok := a.builtin(); ok {
				continue
			}
			if arity, ok := arities[a.name]; ok && arity != len(a.args) {
				s.problem(fmt.Sprintf("%s uses %s with %d blanks or values where it has %d elsewhere", r.name(), a.name, len(a.args), arity))
			}
			arities[a.name] = len(a.args)
			if mangleKeywords[mangleName(a.name)] {
				s.problem(fmt.Sprintf("%s uses %s which mangle keeps for itself", r.name(), a.name))
			}
			for i, t := range a.args {
				if t.kind == blankTerm && strings.HasSuffix(t.text, "fact pattern") {
					if positions[a.predicate()] == nil {
						positions[a.predicate()] = map[int]bool{}
					}
					positions[a.predicate()][i] = true
				}
			}
		}
	}
	var patterns []string
	seenPattern := map[string]bool{}
	for _, r := range s.rules {
		name := textOf(r.name())
		for _, p := range ruleProblems(r) {
			s.problem(p)
		}
		s.observe(atom{name: "has the id", args: []term{name, textOf(r.id())}}, engineFile)
		s.observe(atom{name: "is in the file", args: []term{name, textOf(r.file)}}, engineFile)
		s.observe(atom{name: "defines", args: []term{name, textOf(r.head.name)}}, engineFile)
		s.observe(atom{name: "has a rule for", args: []term{textOf(r.file), textOf(r.head.name)}}, engineFile)
		if r.head.name == "breaks" && len(r.head.args) == 2 && r.head.args[1].kind == textTerm {
			s.observe(atom{name: "lays down", args: []term{name, r.head.args[1]}}, engineFile)
		}
		for _, c := range r.conditions {
			if _, ok := c.atom.builtin(); !ok {
				s.observe(atom{name: "refers to", args: []term{name, textOf(c.atom.name)}}, engineFile)
			}
		}
		for _, blank := range ruleBlanks(r, nil) {
			s.observe(atom{name: "has the blank", args: []term{name, textOf(blank)}}, engineFile)
		}
		if r.readBack() != r.text() {
			s.observe(atom{name: "read back differently", args: []term{name}}, engineFile)
		}
		for _, a := range r.atoms() {
			for i, t := range a.args {
				if positions[a.predicate()][i] && t.kind == textTerm && !seenPattern[t.text] {
					seenPattern[t.text] = true
					patterns = append(patterns, t.text)
				}
			}
		}
	}
	for _, text := range patterns {
		p, err := parsePattern(text)
		if err != nil {
			s.problem(err.Error())
			continue
		}
		pattern := textOf(text)
		s.observe(atom{name: "names", args: []term{pattern, textOf(p.name)}}, engineFile)
		for _, t := range p.args {
			if t.kind == blankTerm {
				s.observe(atom{name: "has the slot", args: []term{pattern, textOf(t.text)}}, engineFile)
			}
		}
	}
	if s.change {
		s.observe(atom{name: "this run is a change"}, engineFile)
	}
}

func declaration(p predicate) string {
	variables := make([]string, p.arity)
	for i := range variables {
		variables[i] = fmt.Sprintf("A%d", i)
	}
	return "Decl " + mangleName(p.name) + "(" + strings.Join(variables, ", ") + ")."
}

func (s *session) program(derive bool) (*analysis.ProgramInfo, error) {
	if info, ok := s.programs[derive]; ok {
		return info, nil
	}
	defined := map[predicate]bool{}
	referenced := map[predicate]bool{}
	for _, r := range s.rules {
		defined[r.head.predicate()] = true
		for _, c := range r.conditions {
			if _, ok := c.atom.builtin(); !ok {
				referenced[c.atom.predicate()] = true
			}
		}
	}
	var undefined []string
	for p := range referenced {
		if !defined[p] {
			undefined = append(undefined, declaration(p))
		}
	}
	sort.Strings(undefined)
	var text strings.Builder
	for _, d := range undefined {
		text.WriteString(d + "\n")
	}
	for _, r := range s.rules {
		text.WriteString(mangleRule(r) + "\n")
	}
	if derive {
		for i, r := range s.rules {
			if len(r.conditions) > 0 {
				text.WriteString(derivationRule(i, r) + "\n")
			}
		}
	}
	unit, err := parse.Unit(strings.NewReader(text.String()))
	if err != nil {
		return nil, err
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		return nil, err
	}
	s.programs[derive] = info
	return info, nil
}

func (s *session) evaluate(extra []atom, derive bool) (*knowledge, error) {
	info, err := s.program(derive)
	if err != nil {
		return nil, err
	}
	facts := append(append([]atom{}, s.observed...), extra...)
	store := factstore.NewSimpleInMemoryStore()
	for _, a := range facts {
		store.Add(toMangle(a))
	}
	if err := engine.EvalProgram(info, store); err != nil {
		return nil, err
	}
	predicates := map[predicate]bool{}
	for _, r := range s.rules {
		for _, a := range r.atoms() {
			if _, ok := a.builtin(); !ok {
				predicates[a.predicate()] = true
			}
		}
	}
	for _, a := range facts {
		predicates[a.predicate()] = true
	}
	k := newKnowledge()
	for p := range predicates {
		query := ast.NewQuery(ast.PredicateSym{Symbol: mangleName(p.name), Arity: p.arity})
		store.GetFacts(query, func(f ast.Atom) error {
			args := make([]term, len(f.Args))
			for i, t := range f.Args {
				args[i] = fromMangle(t)
			}
			k.add(atom{name: p.name, args: args})
			return nil
		})
	}
	if derive {
		for i, r := range s.rules {
			k.derivations = append(k.derivations, derivationsOf(store, i, r)...)
		}
	}
	return k, nil
}

func derivationsOf(store factstore.FactStore, index int, r *rule) []derivation {
	if len(r.conditions) == 0 {
		return []derivation{{fact: r.head, rule: r}}
	}
	names := ruleBlanks(r, hiddenBlanks(r))
	var found []derivation
	query := ast.NewQuery(ast.PredicateSym{Symbol: derivationName(index), Arity: len(names)})
	store.GetFacts(query, func(f ast.Atom) error {
		binding := map[string]term{}
		for i, name := range names {
			binding[name] = fromMangle(f.Args[i])
		}
		d := derivation{fact: substitute(r.head, binding), rule: r}
		for _, c := range r.conditions {
			d.reasons = append(d.reasons, condition{c.negated, substitute(c.atom, binding)})
		}
		found = append(found, d)
		return nil
	})
	sort.Slice(found, func(i, j int) bool {
		return strings.Join(found[i].lines(), "\n") < strings.Join(found[j].lines(), "\n")
	})
	return found
}

func (s *session) settle(k *knowledge) []atom {
	var settled []atom
	check := func(verb, outcome string, wanted bool) {
		for _, a := range k.all(verb, 2) {
			stated := a.args[1]
			f, err := parseFact(stated.plain())
			if err != nil {
				s.problem(fmt.Sprintf("%s cannot be read as a fact: %v", stated.plain(), err))
				continue
			}
			if k.has(f) == wanted {
				settled = append(settled, atom{name: outcome, args: []term{stated}})
			}
		}
	}
	check("expects", "missing", false)
	check("rules out", "present", true)
	return settled
}

func (s *session) reach() (*knowledge, error) {
	for {
		first, err := s.evaluate(nil, false)
		if err != nil {
			return nil, err
		}
		if calls := s.pendingCalls(first); len(calls) > 0 {
			s.runTools(first, calls)
			continue
		}
		settled := s.settle(first)
		final, err := s.evaluate(settled, true)
		if err != nil {
			return nil, err
		}
		if calls := s.pendingCalls(final); len(calls) > 0 {
			s.runTools(final, calls)
			continue
		}
		for _, a := range settled {
			s.observe(a, engineFile)
		}
		return final, nil
	}
}

func (s *session) patternPredicates(k *knowledge, verb string) map[predicate]bool {
	found := map[predicate]bool{}
	for _, a := range k.all(verb, 2) {
		if a.args[0].plain() != theKnowledge {
			continue
		}
		p, err := parsePattern(a.args[1].plain())
		if err != nil {
			s.problem(err.Error())
			continue
		}
		found[p.predicate()] = true
	}
	return found
}

func (s *session) explain(k *knowledge) {
	reasoned := s.patternPredicates(k, "gives reasons for")
	for _, d := range k.derivations {
		if !reasoned[d.fact.predicate()] {
			continue
		}
		for _, reason := range d.reasons {
			a := atom{name: "holds because", args: []term{textOf(d.fact.line()), textOf(reason.line())}}
			s.observe(a, engineFile)
			k.add(a)
		}
	}
}

func (s *session) check(k *knowledge) {
	for _, a := range k.all("means in mangle", 2) {
		said, meant := a.args[0].plain(), a.args[1].plain()
		read, err := mangleLine(said)
		if err != nil {
			s.problem(fmt.Sprintf("%s cannot be read: %v", said, err))
		} else if read != meant {
			s.problem(fmt.Sprintf("%s means %s in mangle but engine.go reads it as %s", said, meant, read))
		}
	}
	for _, a := range k.all("is computed as", 2) {
		if computations[a.args[0].plain()] != a.args[1].plain() {
			s.problem(fmt.Sprintf("engine.go does not compute %s as %s", a.args[0].plain(), a.args[1].plain()))
		}
	}
	for _, p := range describedPredicates {
		for _, a := range k.all(p.name, p.arity) {
			if !selfDescriptions[a.line()] {
				s.problem(fmt.Sprintf("engine.go does not do what %s says", a.line()))
			}
		}
	}
	for _, a := range k.all("is loaded as", 2) {
		if way := a.args[1].plain(); way != plainLoader && way != rowsLoader {
			s.problem(fmt.Sprintf("engine.go cannot load %s as %s", a.args[0].plain(), way))
		}
	}
	for _, a := range k.all("holds", 2) {
		if a.args[0].plain() == theCertificate && !certificateParts[a.args[1].plain()] {
			s.problem(fmt.Sprintf("engine.go cannot put %s in the certificate", a.args[1].plain()))
		}
	}
	_, problems := schema(k.all)
	for _, p := range problems {
		s.problem(p)
	}
}

func (s *session) answer(k *knowledge) string {
	var answers []string
	for _, a := range k.all("conforms", 2) {
		if a.args[0].plain() == theFolder {
			answers = append(answers, a.args[1].plain())
		}
	}
	if len(answers) != 1 {
		s.problem(fmt.Sprintf("the folder has %d answers where it must have one", len(answers)))
	}
	if len(s.problems) > 0 {
		return brokenAnswer
	}
	return answers[0]
}

func exitCode(facts []atom, answer string) int {
	for _, a := range facts {
		if a.args[0].plain() == answer && a.args[1].kind == numberTerm {
			return int(a.args[1].number)
		}
	}
	return 2
}

func problemFact(text string) atom { return atom{name: "a problem", args: []term{textOf(text)}} }

func (s *session) stop() int {
	out := bufio.NewWriter(os.Stdout)
	for _, p := range s.problems {
		fmt.Fprintln(out, problemFact(p).line())
	}
	out.Flush()
	s.withdraw()
	return exitCode(s.stated("exits with", 2), brokenAnswer)
}

func (s *session) print(k *knowledge) {
	shown := s.patternPredicates(k, "shows")
	var lines, verdicts []string
	for _, line := range k.lines() {
		a := k.facts[line]
		if !shown[a.predicate()] {
			continue
		}
		if a.name == "conforms" {
			verdicts = append(verdicts, line)
		} else {
			lines = append(lines, line)
		}
	}
	out := bufio.NewWriter(os.Stdout)
	for _, line := range append(lines, verdicts...) {
		fmt.Fprintln(out, line)
	}
	out.Flush()
}

type column struct {
	number  int64
	name    string
	content string
}

type table struct {
	name    string
	source  string
	columns []column
}

func schema(facts factSource) ([]table, []string) {
	var problems []string
	store := valueOf(facts, "is published to", theKnowledge)
	var tables []table
	for _, a := range facts("has the table", 2) {
		if a.args[0].plain() != store {
			continue
		}
		t := table{name: a.args[1].plain(), source: valueOf(facts, "has a row for", a.args[1].plain())}
		if !sqlName.MatchString(t.name) {
			problems = append(problems, fmt.Sprintf("%s cannot name a table", t.name))
		}
		contents, ok := rowContents[t.source]
		if !ok {
			problems = append(problems, fmt.Sprintf("engine.go cannot make the rows of %s for %s", t.name, t.source))
		}
		numbers := map[int64]bool{}
		for _, c := range facts("has the column", 4) {
			if c.args[0].plain() != t.name {
				continue
			}
			col := column{number: c.args[1].number, name: c.args[2].plain(), content: c.args[3].plain()}
			if c.args[1].kind != numberTerm || numbers[col.number] {
				problems = append(problems, fmt.Sprintf("%s has a column without its own number", t.name))
			}
			numbers[col.number] = true
			if !sqlName.MatchString(col.name) {
				problems = append(problems, fmt.Sprintf("%s cannot name a column", col.name))
			}
			known := false
			for _, content := range contents {
				known = known || content == col.content
			}
			if ok && !known {
				problems = append(problems, fmt.Sprintf("engine.go cannot fill %s with %s", t.name, col.content))
			}
			t.columns = append(t.columns, col)
		}
		sort.Slice(t.columns, func(i, j int) bool { return t.columns[i].number < t.columns[j].number })
		tables = append(tables, t)
	}
	return tables, problems
}

type certificateEntry struct {
	subject string
	value   string
}

func (s *session) certificatePart(k *knowledge, answer, part string) []certificateEntry {
	switch part {
	case levelNamePart:
		return []certificateEntry{{"", s.level}}
	case answerPart:
		return []certificateEntry{{"", answer}}
	case loadedHashPart:
		var entries []certificateEntry
		for _, name := range append(append([]string{}, s.loaded...), s.tested...) {
			entries = append(entries, certificateEntry{name, fileHash(s.path(name))})
		}
		return entries
	case machineHashPart:
		var entries []certificateEntry
		for _, a := range k.all("part of the machine", 1) {
			entries = append(entries, certificateEntry{a.args[0].plain(), fileHash(s.path(a.args[0].plain()))})
		}
		return entries
	}
	return nil
}

func (s *session) rows(k *knowledge, answer, source string) []map[string]any {
	var rows []map[string]any
	switch source {
	case ruleRows:
		for _, r := range s.rules {
			rows = append(rows, map[string]any{
				"the rule id":             r.id(),
				"the rule name":           r.name(),
				"the file the rule is in": r.file,
				"the number of the line the rule starts on": int64(r.line),
				"the rule lines joined by newlines":         r.text(),
			})
		}
	case factRows:
		for _, line := range k.lines() {
			origin, ok := s.origins[line]
			if !ok {
				origin = derivedOrigin
			}
			rows = append(rows, map[string]any{
				"the fact id":                shortHash(line),
				"the fact as one plain line": line,
				"the go file that observed the fact and derived for every other fact": origin,
			})
		}
	case derivationRows:
		for _, d := range k.derivations {
			rows = append(rows, map[string]any{derivationIDValue: d.id(), "the fact id": shortHash(d.fact.line()), "the rule name": d.rule.name()})
		}
	case reasonRows:
		for _, d := range k.derivations {
			for i, reason := range d.reasons {
				rows = append(rows, map[string]any{
					derivationIDValue:                                        d.id(),
					"the number of the condition in the rule":                int64(i + 1),
					"the condition with its blanks filled as one plain line": reason.line(),
				})
			}
		}
	case certificateRows:
		for _, a := range k.all("holds", 2) {
			if a.args[0].plain() != theCertificate {
				continue
			}
			part := a.args[1].plain()
			for _, entry := range s.certificatePart(k, answer, part) {
				rows = append(rows, map[string]any{partContent: part, subjectContent: entry.subject, valueContent: entry.value})
			}
		}
	}
	return rows
}

func (s *session) storePath() string { return filepath.Join(s.root, s.level+".db") }

func (s *session) withdraw() { os.Remove(s.storePath()) }

func (s *session) publish(k *knowledge, answer string) error {
	tables, problems := schema(k.all)
	if len(problems) > 0 {
		return errors.New(problems[0])
	}
	partial := s.storePath() + ".partial"
	os.Remove(partial)
	defer os.Remove(partial)
	db, err := sql.Open("sqlite", partial)
	if err != nil {
		return err
	}
	defer db.Close()
	transaction, err := db.Begin()
	if err != nil {
		return err
	}
	for _, t := range tables {
		rows := s.rows(k, answer, t.source)
		definitions := make([]string, len(t.columns))
		marks := make([]string, len(t.columns))
		for i, c := range t.columns {
			kind := "TEXT"
			if len(rows) > 0 {
				if _, ok := rows[0][c.content].(int64); ok {
					kind = "INTEGER"
				}
			}
			definitions[i] = fmt.Sprintf(`"%s" %s`, c.name, kind)
			marks[i] = "?"
		}
		if _, err := transaction.Exec(fmt.Sprintf(`CREATE TABLE "%s" (%s)`, t.name, strings.Join(definitions, ", "))); err != nil {
			transaction.Rollback()
			return err
		}
		insert, err := transaction.Prepare(fmt.Sprintf(`INSERT INTO "%s" VALUES (%s)`, t.name, strings.Join(marks, ", ")))
		if err != nil {
			transaction.Rollback()
			return err
		}
		for _, row := range rows {
			values := make([]any, len(t.columns))
			for i, c := range t.columns {
				values[i] = row[c.content]
			}
			if _, err := insert.Exec(values...); err != nil {
				insert.Close()
				transaction.Rollback()
				return err
			}
		}
		insert.Close()
	}
	if err := transaction.Commit(); err != nil {
		return err
	}
	if err := db.Close(); err != nil {
		return err
	}
	return os.Rename(partial, s.storePath())
}

func run(arguments []string) int {
	s, err := newSession(arguments)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	s.load()
	s.observeRules()
	if len(s.problems) > 0 {
		return s.stop()
	}
	k, err := s.reach()
	if err != nil {
		s.problem(fmt.Sprintf("mangle cannot evaluate the knowledge: %v", err))
		return s.stop()
	}
	s.check(k)
	s.explain(k)
	answer := s.answer(k)
	if answer == valueOf(k.all, "is published only when", theKnowledge) {
		if err := s.publish(k, answer); err != nil {
			s.problem(fmt.Sprintf("the knowledge cannot be published: %v", err))
			answer = brokenAnswer
			s.withdraw()
		}
	} else {
		s.withdraw()
	}
	for _, p := range s.problems {
		a := problemFact(p)
		s.observe(a, engineFile)
		k.add(a)
	}
	s.print(k)
	return exitCode(k.all("exits with", 2), answer)
}

func main() {
	os.Exit(run(os.Args[1:]))
}
