package main

import (
	"crypto/sha256"
	"database/sql"
	"encoding/hex"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	mangle "codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	_ "modernc.org/sqlite"
)

const (
	engineFile     = "engine.go"
	toolsFile      = "tools.go"
	firstFile      = "spec.plain"
	changeVariable = "PLAIN_CHANGE"
	knowledgeView  = "the knowledge view"
	ruleIDKind     = "a rule id"
	factIDKind     = "a fact id"
	ruleIDMethod   = "the first 16 hex digits of the sha256 of the rule lines joined by newlines"
	factIDMethod   = "the first 16 hex digits of the sha256 of the fact as one plain line"
	rulesKind      = "every rule with its id"
	factsKind      = "every fact with its id"
	reasonsKind    = "every reason for every derived fact"
	certificate    = "the certificate"
	hashesPart     = "the hash of every file engine.go loads"
	answerPart     = "the answer"
)

var engineExecutes = []string{
	"loads/2", "means_in_mangle/2", "calls/3", "exits_with/2", "conforms/2", "a_problem/1",
	"prints/2", "prints_in/2", "prints_to/2", "in_the_knowledge_view/1", "shows/2",
	"gives_reasons_for/2", "is_published_to/2", "is_published_only_when/2",
	"is_the_sqlite_file/2", "keeps/2", "holds/2", "is_computed_as/2", "creates_fact/2",
}

var engineCreates = []string{
	"this_run_is_a_change/0", "a_problem/1", "read_back_differently/1", "has_a_rule_for/2",
	"defines/2", "refers_to/2", "lays_down/2", "names/2", "has_the_blank/2", "has_the_slot/2",
	"holds_because/2", "has_the_id/2",
}

const (
	textValue = iota
	numberValue
	blankValue
)

type value struct {
	kind int
	text string
	num  int64
}

func text(s string) value { return value{kind: textValue, text: s} }

func number(n int64) value { return value{kind: numberValue, num: n} }

func (v value) key() string {
	switch v.kind {
	case numberValue:
		return "n" + strconv.FormatInt(v.num, 10)
	case blankValue:
		return "b" + v.text
	}
	return "s" + v.text
}

func (v value) words() string {
	if v.kind == numberValue {
		return strconv.FormatInt(v.num, 10)
	}
	return v.text
}

func (v value) plain() string {
	switch v.kind {
	case numberValue:
		return strconv.FormatInt(v.num, 10)
	case blankValue:
		return "[" + v.text + "]"
	}
	return quote(v.text)
}

func (v value) mangle() string {
	switch v.kind {
	case numberValue:
		return ast.Number(v.num).String()
	case blankValue:
		return variable(v.text)
	}
	return ast.String(v.text).String()
}

func variable(name string) string {
	var b strings.Builder
	for _, w := range strings.Fields(name) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	return b.String()
}

var (
	wordsPattern  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	blankPattern  = regexp.MustCompile(`^\[([^\[\]]*)\]$`)
	numberPattern = regexp.MustCompile(`^-?(0|[1-9][0-9]*)$`)
)

func needsQuotes(s string) bool {
	return s == "" || s != strings.TrimSpace(s) || strings.ContainsAny(s, ",\n\r") ||
		strings.HasPrefix(s, `"`) || strings.HasPrefix(s, "'") || strings.HasPrefix(s, "not ") ||
		blankPattern.MatchString(s) || numberPattern.MatchString(s)
}

func quote(s string) string {
	if !needsQuotes(s) {
		return s
	}
	s = strings.NewReplacer("\r\n", " ", "\n", " ", "\r", " ").Replace(s)
	switch {
	case !strings.Contains(s, `"`):
		return `"` + s + `"`
	case !strings.Contains(s, "'"):
		return "'" + s + "'"
	}
	return `"` + strings.ReplaceAll(s, `"`, "'") + `"`
}

func flat(s string) string { return strings.Join(strings.Fields(s), " ") }

func shortHash(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])[:16]
}

func idValue(id string) value {
	if numberPattern.MatchString(id) {
		if n, err := strconv.ParseInt(id, 10, 64); err == nil {
			return number(n)
		}
	}
	return text(id)
}

type rawPart struct {
	text   string
	quoted bool
}

func splitParts(s string) ([]rawPart, error) {
	var parts []rawPart
	i := 0
	for {
		for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i < len(s) && (s[i] == '"' || s[i] == '\'') {
			end := strings.IndexByte(s[i+1:], s[i])
			if end < 0 {
				return nil, errors.New("a quote is not closed")
			}
			parts = append(parts, rawPart{s[i+1 : i+1+end], true})
			i += end + 2
			for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
				i++
			}
			if i == len(s) {
				return parts, nil
			}
			if s[i] != ',' {
				return nil, errors.New("a quoted part must end at a comma")
			}
			i++
			continue
		}
		end := strings.IndexByte(s[i:], ',')
		piece := s[i:]
		if end >= 0 {
			piece = s[i : i+end]
		}
		piece = strings.TrimSpace(piece)
		if piece == "" {
			return nil, errors.New("a part is empty")
		}
		parts = append(parts, rawPart{piece, false})
		if end < 0 {
			return parts, nil
		}
		i += end + 1
	}
}

func parseValue(p rawPart) (value, error) {
	if p.quoted {
		return text(p.text), nil
	}
	if m := blankPattern.FindStringSubmatch(p.text); m != nil {
		if !wordsPattern.MatchString(m[1]) {
			return value{}, fmt.Errorf("the blank %s is not named in plain words", p.text)
		}
		return value{kind: blankValue, text: m[1]}, nil
	}
	if numberPattern.MatchString(p.text) {
		if n, err := strconv.ParseInt(p.text, 10, 64); err == nil {
			return number(n), nil
		}
	}
	return text(p.text), nil
}

func predicateName(words string) (string, bool) {
	if !wordsPattern.MatchString(words) {
		return "", false
	}
	return strings.ReplaceAll(words, " ", "_"), true
}

func predicateWords(pred string) string { return strings.ReplaceAll(pred, "_", " ") }

func predKey(pred string, arity int) string { return pred + "/" + strconv.Itoa(arity) }

var builtinVerbs = map[string]bool{"ends with": true, "starts with": true, "differs from": true, "is the join of": true}

type atom struct {
	negated bool
	builtin string
	pred    string
	args    []value
}

func parseAtom(line string, builtinsAllowed bool) (atom, error) {
	parts, err := splitParts(line)
	if err != nil {
		return atom{}, err
	}
	if len(parts) == 1 {
		name, ok := predicateName(parts[0].text)
		if parts[0].quoted || !ok {
			return atom{}, errors.New("a line with one part must be plain words")
		}
		return atom{pred: name}, nil
	}
	if len(parts) == 2 {
		return atom{}, errors.New("a line needs one part or at least three parts")
	}
	values := make([]value, len(parts))
	for i, p := range parts {
		if values[i], err = parseValue(p); err != nil {
			return atom{}, err
		}
	}
	verb := values[1]
	if verb.kind != textValue {
		return atom{}, errors.New("the second part must be words")
	}
	args := append([]value{values[0]}, values[2:]...)
	if builtinVerbs[verb.text] {
		if !builtinsAllowed {
			return atom{}, fmt.Errorf("%s can only be a condition", verb.text)
		}
		if verb.text != "is the join of" && len(values) != 3 {
			return atom{}, fmt.Errorf("%s needs three parts", verb.text)
		}
		return atom{builtin: verb.text, args: args}, nil
	}
	if verb.text == "is" {
		if len(values) != 3 || values[2].kind != textValue {
			return atom{}, errors.New("a line with is needs three parts and words at the end")
		}
		name, ok := predicateName(values[2].text)
		if !ok {
			return atom{}, fmt.Errorf("%s is not plain words", values[2].text)
		}
		return atom{pred: name, args: args[:1]}, nil
	}
	name, ok := predicateName(verb.text)
	if !ok {
		return atom{}, fmt.Errorf("%s is not plain words", verb.text)
	}
	return atom{pred: name, args: args}, nil
}

func (a atom) plain() string {
	var parts []string
	switch {
	case a.builtin != "":
		parts = append(parts, a.args[0].plain(), a.builtin)
		for _, v := range a.args[1:] {
			parts = append(parts, v.plain())
		}
	case len(a.args) == 0:
		parts = append(parts, predicateWords(a.pred))
	case len(a.args) == 1:
		parts = append(parts, a.args[0].plain(), "is", predicateWords(a.pred))
	default:
		parts = append(parts, a.args[0].plain(), predicateWords(a.pred))
		for _, v := range a.args[1:] {
			parts = append(parts, v.plain())
		}
	}
	return strings.Join(parts, ", ")
}

func (a atom) mangle() string {
	args := make([]string, len(a.args))
	for i, v := range a.args {
		args[i] = v.mangle()
	}
	switch a.builtin {
	case "ends with":
		return ":string:ends_with(" + strings.Join(args, ", ") + ")"
	case "starts with":
		return ":string:starts_with(" + strings.Join(args, ", ") + ")"
	case "differs from":
		return args[0] + " != " + args[1]
	case "is the join of":
		return args[0] + " = fn:string:concat(" + strings.Join(args[1:], ", ") + ")"
	}
	s := a.pred + "(" + strings.Join(args, ", ") + ")"
	if a.negated {
		s = "!" + s
	}
	return s
}

func (a atom) ground() bool {
	for _, v := range a.args {
		if v.kind == blankValue {
			return false
		}
	}
	return true
}

func translateLine(line string) (string, error) {
	a, err := parseAtom(line, true)
	if err != nil {
		return "", err
	}
	if a.builtin != "" {
		return a.mangle(), nil
	}
	return a.mangle() + ".", nil
}

type statement struct {
	file  string
	line  int
	lines []string
	head  atom
	conds []atom
	gap   bool
	bad   bool
}

func (s *statement) name() string { return s.file + ":" + strconv.Itoa(s.line) }

func (s *statement) id() string { return shortHash(strings.Join(s.lines, "\n")) }

func (s *statement) plain() string {
	lines := []string{s.head.plain()}
	for i, c := range s.conds {
		word := "and "
		if i == 0 {
			word = "if "
		}
		if c.negated {
			word += "not "
		}
		lines = append(lines, "    "+word+c.plain())
	}
	return strings.Join(lines, "\n")
}

func (s *statement) mangle() string {
	if len(s.conds) == 0 {
		return s.head.mangle() + "."
	}
	body := make([]string, len(s.conds))
	for i, c := range s.conds {
		body[i] = c.mangle()
	}
	return s.head.mangle() + " :- " + strings.Join(body, ", ") + "."
}

func (s *statement) blanks() []string {
	seen := map[string]bool{}
	var out []string
	for _, a := range append([]atom{s.head}, s.conds...) {
		for _, v := range a.args {
			if v.kind == blankValue && !seen[v.text] {
				seen[v.text] = true
				out = append(out, v.text)
			}
		}
	}
	return out
}

func (s *statement) unbound() []string {
	bound := map[string]bool{}
	for _, c := range s.conds {
		if c.builtin == "" && !c.negated {
			for _, v := range c.args {
				if v.kind == blankValue {
					bound[v.text] = true
				}
			}
		}
	}
	for changed := true; changed; {
		changed = false
		for _, c := range s.conds {
			if c.builtin != "is the join of" || c.args[0].kind != blankValue || bound[c.args[0].text] {
				continue
			}
			ready := true
			for _, v := range c.args[1:] {
				if v.kind == blankValue && !bound[v.text] {
					ready = false
				}
			}
			if ready {
				bound[c.args[0].text] = true
				changed = true
			}
		}
	}
	seen := map[string]bool{}
	var missing []string
	check := func(v value) {
		if v.kind == blankValue && !bound[v.text] && !seen[v.text] {
			seen[v.text] = true
			missing = append(missing, "["+v.text+"]")
		}
	}
	for _, v := range s.head.args {
		check(v)
	}
	for _, c := range s.conds {
		if c.negated || c.builtin != "" {
			for _, v := range c.args {
				check(v)
			}
		}
	}
	return missing
}

func parseCondition(line string, first bool) (atom, error) {
	var rest string
	switch {
	case strings.HasPrefix(line, "if "):
		if !first {
			return atom{}, errors.New("only the first condition starts with if")
		}
		rest = line[3:]
	case strings.HasPrefix(line, "and "):
		if first {
			return atom{}, errors.New("the first condition starts with if")
		}
		rest = line[4:]
	default:
		return atom{}, errors.New("a condition starts with if or and")
	}
	negated := strings.HasPrefix(rest, "not ")
	if negated {
		rest = rest[4:]
	}
	a, err := parseAtom(rest, true)
	if err != nil {
		return atom{}, err
	}
	if negated && a.builtin != "" {
		return atom{}, errors.New("a builtin condition cannot be negated")
	}
	a.negated = negated
	return a, nil
}

func parseText(file, content string) ([]*statement, []string) {
	var all []*statement
	var problems []string
	var current *statement
	skipping := false
	gap := true
	lines := strings.Split(content, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	for i, line := range lines {
		where := file + ":" + strconv.Itoa(i+1) + ": "
		if strings.TrimSpace(line) == "" {
			current, skipping, gap = nil, false, true
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			if current == nil {
				if !skipping {
					problems = append(problems, where+"a condition must follow a rule")
					skipping = true
				}
				continue
			}
			c, err := parseCondition(strings.TrimLeft(line, " \t"), len(current.conds) == 0)
			if err != nil {
				problems = append(problems, where+err.Error())
				current.bad = true
				current, skipping = nil, true
				continue
			}
			current.conds = append(current.conds, c)
			current.lines = append(current.lines, line)
			continue
		}
		head, err := parseAtom(line, false)
		if err != nil {
			problems = append(problems, where+err.Error())
			current, skipping = nil, true
			continue
		}
		current = &statement{file: file, line: i + 1, lines: []string{line}, head: head, gap: gap}
		all = append(all, current)
		gap, skipping = false, false
	}
	var out []*statement
	for _, s := range all {
		if s.bad {
			continue
		}
		if missing := s.unbound(); len(missing) > 0 {
			problems = append(problems, s.name()+": "+strings.Join(missing, ", ")+" must be bound by a condition")
			continue
		}
		out = append(out, s)
	}
	return out, problems
}

type pattern struct {
	text  string
	pred  string
	slots []string
}

func parsePattern(s string) (pattern, error) {
	type piece struct {
		slot bool
		text string
	}
	var pieces []piece
	rest := s
	for rest != "" {
		i := strings.IndexByte(rest, '[')
		if i < 0 {
			if t := strings.TrimSpace(rest); t != "" {
				pieces = append(pieces, piece{false, t})
			}
			break
		}
		if t := strings.TrimSpace(rest[:i]); t != "" {
			pieces = append(pieces, piece{false, t})
		}
		j := strings.IndexByte(rest[i:], ']')
		if j < 0 {
			return pattern{}, fmt.Errorf("the fact pattern %s has a slot that is not closed", s)
		}
		name := rest[i+1 : i+j]
		if !wordsPattern.MatchString(name) {
			return pattern{}, fmt.Errorf("the fact pattern %s has a slot that is not plain words", s)
		}
		pieces = append(pieces, piece{true, name})
		rest = rest[i+j+1:]
	}
	bad := fmt.Errorf("the fact pattern %s is not a slot, words and slots", s)
	if len(pieces) == 1 && !pieces[0].slot {
		name, ok := predicateName(pieces[0].text)
		if !ok {
			return pattern{}, bad
		}
		return pattern{text: s, pred: name}, nil
	}
	if len(pieces) < 2 || !pieces[0].slot || pieces[1].slot || builtinVerbs[pieces[1].text] {
		return pattern{}, bad
	}
	slots := []string{pieces[0].text}
	for _, p := range pieces[2:] {
		if !p.slot {
			return pattern{}, bad
		}
		slots = append(slots, p.text)
	}
	verb := pieces[1].text
	if len(slots) == 1 && strings.HasPrefix(verb, "is ") {
		verb = verb[3:]
	} else if len(slots) == 1 || verb == "is" {
		return pattern{}, bad
	}
	name, ok := predicateName(verb)
	if !ok {
		return pattern{}, bad
	}
	return pattern{text: s, pred: name, slots: slots}, nil
}

func (p pattern) key() string { return predKey(p.pred, len(p.slots)) }

func isPatternBlank(name string) bool {
	return name == "fact pattern" || name == "any fact pattern" || name == "other fact pattern"
}

func collectPatterns(stmts []*statement) ([]pattern, []string) {
	positions := map[string]bool{}
	var atoms []atom
	for _, s := range stmts {
		for _, a := range append([]atom{s.head}, s.conds...) {
			if a.builtin != "" {
				continue
			}
			atoms = append(atoms, a)
			for i, v := range a.args {
				if v.kind == blankValue && isPatternBlank(v.text) {
					positions[predKey(a.pred, len(a.args))+"#"+strconv.Itoa(i)] = true
				}
			}
		}
	}
	seen := map[string]bool{}
	var found []pattern
	var problems []string
	for changed := true; changed; {
		changed = false
		for _, a := range atoms {
			for i, v := range a.args {
				if v.kind != textValue || seen[v.text] || !positions[predKey(a.pred, len(a.args))+"#"+strconv.Itoa(i)] {
					continue
				}
				seen[v.text] = true
				changed = true
				p, err := parsePattern(v.text)
				if err != nil {
					problems = append(problems, err.Error())
					continue
				}
				found = append(found, p)
				for j, slot := range p.slots {
					if slot == "fact pattern" {
						positions[p.key()+"#"+strconv.Itoa(j)] = true
					}
				}
			}
		}
	}
	sort.Slice(found, func(i, j int) bool { return found[i].text < found[j].text })
	return found, problems
}

type fact struct {
	pred string
	args []value
}

func (f fact) atom() atom { return atom{pred: f.pred, args: f.args} }

func (f fact) plain() string { return f.atom().plain() }

func (f fact) key() string {
	keys := make([]string, len(f.args))
	for i, v := range f.args {
		keys[i] = v.key()
	}
	return predKey(f.pred, len(f.args)) + "(" + strings.Join(keys, "\x00") + ")"
}

type model struct {
	byPred  map[string][]fact
	byFirst map[string][]fact
	all     map[string]bool
}

func newModel() *model {
	return &model{byPred: map[string][]fact{}, byFirst: map[string][]fact{}, all: map[string]bool{}}
}

func (m *model) add(f fact) bool {
	k := f.key()
	if m.all[k] {
		return false
	}
	m.all[k] = true
	pk := predKey(f.pred, len(f.args))
	m.byPred[pk] = append(m.byPred[pk], f)
	if len(f.args) > 0 {
		m.byFirst[pk+"\x00"+f.args[0].key()] = append(m.byFirst[pk+"\x00"+f.args[0].key()], f)
	}
	return true
}

func (m *model) has(f fact) bool { return m.all[f.key()] }

func (m *model) get(pred string, arity int) []fact { return m.byPred[predKey(pred, arity)] }

func (m *model) objects(pred string, subject value) []value {
	var out []value
	for _, f := range m.byFirst[predKey(pred, 2)+"\x00"+subject.key()] {
		out = append(out, f.args[1])
	}
	return out
}

func (m *model) sorted() []fact {
	var out []fact
	for _, fs := range m.byPred {
		out = append(out, fs...)
	}
	sortFacts(out)
	return out
}

func sortFacts(fs []fact) {
	sort.Slice(fs, func(i, j int) bool {
		if fs[i].pred != fs[j].pred {
			return fs[i].pred < fs[j].pred
		}
		return fs[i].plain() < fs[j].plain()
	})
}

func single(vs []value) (value, bool) {
	if len(vs) != 1 {
		return value{}, false
	}
	return vs[0], true
}

func evaluate(program string) (m *model, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("%v", r)
		}
	}()
	unit, err := parse.Unit(strings.NewReader(program))
	if err != nil {
		return nil, err
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		return nil, err
	}
	store := factstore.NewSimpleInMemoryStore()
	if err := mangle.EvalProgram(info, store); err != nil {
		return nil, err
	}
	m = newModel()
	for _, p := range store.ListPredicates() {
		err := store.GetFacts(ast.NewQuery(p), func(a ast.Atom) error {
			args := make([]value, len(a.Args))
			for i, t := range a.Args {
				c, ok := t.(ast.Constant)
				switch {
				case !ok:
					args[i] = text(t.String())
				case c.Type == ast.NumberType:
					args[i] = number(c.NumValue)
				case c.Type == ast.StringType:
					args[i] = text(c.Symbol)
				default:
					args[i] = text(c.String())
				}
			}
			m.add(fact{p.Symbol, args})
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	return m, nil
}

func buildProgram(stmts []*statement, facts []fact) string {
	defined := map[string]bool{}
	arity := map[string]int{}
	names := map[string]string{}
	for _, s := range stmts {
		defined[predKey(s.head.pred, len(s.head.args))] = true
		for _, c := range s.conds {
			if c.builtin == "" {
				k := predKey(c.pred, len(c.args))
				arity[k], names[k] = len(c.args), c.pred
			}
		}
	}
	for _, f := range facts {
		defined[predKey(f.pred, len(f.args))] = true
	}
	var keys []string
	for k := range names {
		if !defined[k] {
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	var b strings.Builder
	for _, k := range keys {
		vars := make([]string, arity[k])
		for i := range vars {
			vars[i] = "A" + strconv.Itoa(i)
		}
		fmt.Fprintf(&b, "Decl %s(%s).\n", names[k], strings.Join(vars, ", "))
	}
	for _, s := range stmts {
		b.WriteString(s.mangle() + "\n")
	}
	for _, f := range facts {
		b.WriteString(f.atom().mangle() + ".\n")
	}
	return b.String()
}

type runner struct {
	change     bool
	loaded     []string
	contents   map[string][]byte
	statements []*statement
	byHead     map[string][]*statement
	problems   []string
	created    []fact
	results    []fact
	done       map[string]bool
	order      map[string]int
	model      *model
}

func (r *runner) load() {
	r.contents = map[string][]byte{}
	r.statements, r.problems = nil, nil
	for _, file := range r.loaded {
		data, err := os.ReadFile(file)
		if err != nil {
			if !errors.Is(err, fs.ErrNotExist) {
				r.problems = append(r.problems, file+" cannot be read: "+flat(err.Error()))
			}
			continue
		}
		r.contents[file] = data
		stmts, problems := parseText(file, string(data))
		r.statements = append(r.statements, stmts...)
		r.problems = append(r.problems, problems...)
	}
	r.byHead = map[string][]*statement{}
	r.order = map[string]int{}
	for i, s := range r.statements {
		k := predKey(s.head.pred, len(s.head.args))
		r.byHead[k] = append(r.byHead[k], s)
		if len(s.conds) == 0 && s.head.ground() {
			fk := fact{s.head.pred, s.head.args}.key()
			if _, ok := r.order[fk]; !ok {
				r.order[fk] = i
			}
		}
	}
}

func (r *runner) create() {
	seen := map[string]bool{}
	var out []fact
	add := func(pred string, args ...value) {
		f := fact{pred, args}
		if !seen[f.key()] {
			seen[f.key()] = true
			out = append(out, f)
		}
	}
	if r.change {
		add("this_run_is_a_change")
	}
	for _, s := range r.statements {
		name := text(s.name())
		add("has_a_rule_for", text(s.file), text(s.head.pred))
		add("defines", name, text(s.head.pred))
		for _, c := range s.conds {
			if c.builtin == "" {
				add("refers_to", name, text(c.pred))
			}
		}
		if s.head.pred == "breaks" && len(s.head.args) == 2 && s.head.args[1].kind != blankValue {
			add("lays_down", name, s.head.args[1])
		}
		for _, b := range s.blanks() {
			add("has_the_blank", name, text(b))
		}
		add("has_the_id", name, idValue(s.id()))
		if s.plain() != strings.Join(s.lines, "\n") {
			add("read_back_differently", name)
		}
	}
	patterns, problems := collectPatterns(r.statements)
	r.problems = append(r.problems, problems...)
	for _, p := range patterns {
		add("names", text(p.text), text(p.pred))
		for _, slot := range p.slots {
			add("has_the_slot", text(p.text), text(slot))
		}
	}
	for _, p := range r.problems {
		add("a_problem", text(p))
	}
	r.created = out
}

func (r *runner) step() (bool, error) {
	r.load()
	r.create()
	m, err := evaluate(buildProgram(r.statements, append(append([]fact{}, r.created...), r.results...)))
	if err != nil {
		r.model = newModel()
		for _, f := range r.created {
			r.model.add(f)
		}
		return false, err
	}
	r.model = m
	more := false
	var files []string
	for _, f := range m.get("loads", 2) {
		if f.args[0].key() != text(engineFile).key() || f.args[1].kind != textValue {
			continue
		}
		known := false
		for _, l := range r.loaded {
			known = known || l == f.args[1].text
		}
		if !known {
			files = append(files, f.args[1].text)
		}
	}
	sort.Strings(files)
	if len(files) > 0 {
		r.loaded = append(r.loaded, files...)
		more = true
	}
	var calls []fact
	for _, f := range m.get("calls", 3) {
		if !r.done[f.key()] {
			r.done[f.key()] = true
			calls = append(calls, f)
		}
	}
	sortFacts(calls)
	if len(calls) > 0 {
		more = true
		returned := make([][]result, len(calls))
		var wg sync.WaitGroup
		limit := make(chan struct{}, runtime.NumCPU())
		for i, c := range calls {
			if c.args[1].kind != textValue {
				continue
			}
			wg.Add(1)
			go func(i int, c fact) {
				defer wg.Done()
				defer func() { recover() }()
				limit <- struct{}{}
				defer func() { <-limit }()
				returned[i] = runTool(c.args[1].text, c.args[2], m, r.order)
			}(i, c)
		}
		wg.Wait()
		for i, c := range calls {
			for _, res := range returned[i] {
				r.results = append(r.results, fact{"returned", []value{c.args[0], text(res.field), res.value}})
			}
		}
	}
	return more, nil
}

func (r *runner) problem(p string) {
	r.model.add(fact{"a_problem", []value{text(flat(p))}})
}

func (r *runner) reasons(f fact) [][]fact {
	var out [][]fact
	for _, s := range r.byHead[predKey(f.pred, len(f.args))] {
		b := map[string]value{}
		ok := true
		for i, v := range s.head.args {
			ok = ok && bind(b, v, f.args[i])
		}
		if ok {
			r.model.solve(s.conds, b, nil, &out)
		}
	}
	return out
}

func (r *runner) reasonsBy(f fact) map[*statement][][]fact {
	out := map[*statement][][]fact{}
	for _, s := range r.byHead[predKey(f.pred, len(f.args))] {
		b := map[string]value{}
		ok := true
		for i, v := range s.head.args {
			ok = ok && bind(b, v, f.args[i])
		}
		if !ok {
			continue
		}
		var sols [][]fact
		r.model.solve(s.conds, b, nil, &sols)
		if len(sols) > 0 {
			out[s] = sols
		}
	}
	return out
}

func bind(b map[string]value, pat, v value) bool {
	if pat.kind != blankValue {
		return pat.key() == v.key()
	}
	if old, ok := b[pat.text]; ok {
		return old.key() == v.key()
	}
	b[pat.text] = v
	return true
}

func copyBinding(b map[string]value) map[string]value {
	out := make(map[string]value, len(b))
	for k, v := range b {
		out[k] = v
	}
	return out
}

func lookup(b map[string]value, v value) (value, bool) {
	if v.kind != blankValue {
		return v, true
	}
	x, ok := b[v.text]
	return x, ok
}

func ready(c atom, b map[string]value) bool {
	args := c.args
	if c.builtin == "is the join of" {
		args = args[1:]
	}
	for _, v := range args {
		if _, ok := lookup(b, v); !ok {
			return false
		}
	}
	return true
}

func (m *model) solve(conds []atom, b map[string]value, acc []fact, out *[][]fact) {
	if len(conds) == 0 {
		*out = append(*out, append([]fact(nil), acc...))
		return
	}
	pick := -1
	for i, c := range conds {
		if (c.builtin == "" && !c.negated) || ready(c, b) {
			pick = i
			break
		}
	}
	if pick < 0 {
		return
	}
	c := conds[pick]
	rest := append(append([]atom{}, conds[:pick]...), conds[pick+1:]...)
	switch {
	case c.builtin != "":
		if nb, ok := m.builtin(c, b); ok {
			m.solve(rest, nb, acc, out)
		}
	case c.negated:
		args := make([]value, len(c.args))
		for i, v := range c.args {
			args[i], _ = lookup(b, v)
		}
		if !m.has(fact{c.pred, args}) {
			m.solve(rest, b, acc, out)
		}
	default:
		candidates := m.get(c.pred, len(c.args))
		if len(c.args) > 0 {
			if first, ok := lookup(b, c.args[0]); ok {
				candidates = m.byFirst[predKey(c.pred, len(c.args))+"\x00"+first.key()]
			}
		}
		for _, f := range candidates {
			nb := copyBinding(b)
			ok := true
			for i, v := range c.args {
				ok = ok && bind(nb, v, f.args[i])
			}
			if ok {
				m.solve(rest, nb, append(append([]fact{}, acc...), f), out)
			}
		}
	}
}

func (m *model) builtin(c atom, b map[string]value) (map[string]value, bool) {
	if c.builtin == "is the join of" {
		var sb strings.Builder
		for _, p := range c.args[1:] {
			v, _ := lookup(b, p)
			sb.WriteString(v.words())
		}
		nb := copyBinding(b)
		return nb, bind(nb, c.args[0], text(sb.String()))
	}
	x, _ := lookup(b, c.args[0])
	y, _ := lookup(b, c.args[1])
	switch c.builtin {
	case "differs from":
		return b, x.key() != y.key()
	case "ends with":
		return b, x.kind == textValue && y.kind == textValue && strings.HasSuffix(x.text, y.text)
	case "starts with":
		return b, x.kind == textValue && y.kind == textValue && strings.HasPrefix(x.text, y.text)
	}
	return nil, false
}

func (r *runner) checkTranslations() {
	for _, f := range r.model.get("means_in_mangle", 2) {
		line, want := f.args[0], f.args[1]
		if line.kind != textValue || want.kind != textValue {
			r.problem(f.plain() + " needs a line and its mangle")
			continue
		}
		got, err := translateLine(line.text)
		if err != nil {
			r.problem(line.text + " cannot be read: " + err.Error())
			continue
		}
		if got != want.text {
			r.problem(line.text + " means in mangle " + got + " and not " + want.text)
		}
	}
}

func (r *runner) checkMachine() {
	implemented := map[string][]string{engineFile: engineExecutes, toolsFile: toolsExecutes}
	creating := map[string][]string{engineFile: engineCreates, toolsFile: toolsCreates}
	check := func(pred string, files map[string][]string, verb string) {
		declared := map[string]map[string]bool{}
		for _, f := range r.model.get(pred, 2) {
			name := f.args[0].words()
			if _, ok := files[name]; !ok || f.args[0].kind != textValue || f.args[1].kind != textValue {
				continue
			}
			p, err := parsePattern(f.args[1].text)
			if err != nil {
				continue
			}
			if declared[name] == nil {
				declared[name] = map[string]bool{}
			}
			declared[name][p.key()] = true
			can := false
			for _, k := range files[name] {
				can = can || k == p.key()
			}
			if !can {
				r.problem(name + " does not " + verb + " " + f.args[1].text)
			}
		}
		var names []string
		for name := range files {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			for _, k := range files[name] {
				if !declared[name][k] {
					r.problem(name + " does " + verb + " " + predicateWords(strings.Split(k, "/")[0]) + " but no fact says so")
				}
			}
		}
	}
	check("executes_instruction", implemented, "execute")
	check("creates_fact", creating, "create")
}

func (r *runner) checkInstructions() {
	me := text(engineFile)
	for _, v := range r.model.objects("prints", me) {
		if v.words() != knowledgeView {
			r.problem(engineFile + " cannot print " + v.words())
		}
	}
	for _, v := range r.model.objects("prints_in", me) {
		if v.words() != "plain language" {
			r.problem(engineFile + " cannot print in " + v.words())
		}
	}
	for _, v := range r.model.objects("prints_to", me) {
		if v.words() != "standard output" && v.words() != "standard error" {
			r.problem(engineFile + " cannot print to " + v.words())
		}
	}
	for _, f := range r.model.get("is_computed_as", 2) {
		kind, method := f.args[0].words(), f.args[1].words()
		switch {
		case kind == ruleIDKind && method == ruleIDMethod:
		case kind == factIDKind && method == factIDMethod:
		default:
			r.problem(engineFile + " cannot compute " + kind + " as " + method)
		}
	}
	for _, f := range r.model.get("is_published_to", 2) {
		if f.args[0].words() != knowledgeView {
			r.problem(engineFile + " cannot publish " + f.args[0].words())
		}
		if _, ok := single(r.model.objects("is_the_sqlite_file", f.args[1])); !ok {
			r.problem(f.args[1].words() + " needs exactly one sqlite file")
		}
	}
	for _, f := range r.model.get("keeps", 2) {
		switch f.args[1].words() {
		case rulesKind, factsKind, reasonsKind, certificate:
		default:
			r.problem(engineFile + " cannot keep " + f.args[1].words())
		}
	}
	for _, v := range r.model.objects("holds", text(certificate)) {
		if v.words() != hashesPart && v.words() != answerPart {
			r.problem(engineFile + " cannot put " + v.words() + " in " + certificate)
		}
	}
}

func (r *runner) giveReasons() {
	var added []fact
	for _, f := range r.model.get("gives_reasons_for", 2) {
		p, err := parsePattern(f.args[1].words())
		if err != nil {
			continue
		}
		for _, derived := range r.model.get(p.pred, len(p.slots)) {
			for _, premises := range r.reasons(derived) {
				for _, premise := range premises {
					added = append(added, fact{"holds_because", []value{text(derived.plain()), text(premise.plain())}})
				}
			}
		}
	}
	for _, f := range added {
		r.model.add(f)
	}
}

func (r *runner) answer() (string, int) {
	answer := ""
	var answers []value
	seen := map[string]bool{}
	for _, f := range r.model.get("conforms", 2) {
		if !seen[f.args[1].key()] {
			seen[f.args[1].key()] = true
			answers = append(answers, f.args[1])
		}
	}
	if len(answers) == 1 && answers[0].kind == textValue {
		answer = answers[0].text
	} else {
		r.problem("the folder must conform with exactly one answer")
	}
	if len(r.model.get("a_problem", 1)) > 0 {
		answer = "broken"
	}
	code, ok := r.exitCode(answer)
	if !ok && answer != "broken" {
		r.problem(answer + " has no exit code")
		answer = "broken"
		code, ok = r.exitCode(answer)
	}
	if !ok {
		code = 2
	}
	return answer, code
}

func (r *runner) exitCode(answer string) (int, bool) {
	codes := r.model.objects("exits_with", text(answer))
	if c, ok := single(codes); ok && c.kind == numberValue {
		return int(c.num), true
	}
	return 0, false
}

func (r *runner) render(view string) string {
	var b strings.Builder
	first := true
	for _, s := range r.statements {
		if !r.model.has(fact{"in_the_knowledge_view", []value{text(s.name())}}) {
			continue
		}
		if s.gap && !first {
			b.WriteString("\n")
		}
		b.WriteString(s.plain() + "\n")
		first = false
	}
	groups := map[string]pattern{}
	for _, v := range r.model.objects("shows", text(view)) {
		if p, err := parsePattern(v.words()); err == nil {
			groups[p.key()] = p
		}
	}
	var keys []string
	for k := range groups {
		keys = append(keys, k)
	}
	rank := func(k string) int {
		if r.model.has(fact{"observed", []value{text(groups[k].pred)}}) {
			return 0
		}
		for _, e := range engineExecutes {
			if e == k {
				return 2
			}
		}
		return 1
	}
	sort.Slice(keys, func(i, j int) bool {
		if rank(keys[i]) != rank(keys[j]) {
			return rank(keys[i]) < rank(keys[j])
		}
		return keys[i] < keys[j]
	})
	for _, k := range keys {
		p := groups[k]
		var lines []string
		for _, f := range r.model.get(p.pred, len(p.slots)) {
			lines = append(lines, f.plain())
		}
		if len(lines) == 0 {
			continue
		}
		sort.Strings(lines)
		if !first {
			b.WriteString("\n")
		}
		b.WriteString(strings.Join(lines, "\n") + "\n")
		first = false
	}
	return b.String()
}

func (r *runner) publish(answer string) {
	for _, f := range r.model.get("is_published_to", 2) {
		view, store := f.args[0], f.args[1]
		conditions := r.model.objects("is_published_only_when", view)
		allowed := len(conditions) == 0
		for _, c := range conditions {
			allowed = allowed || c.words() == answer
		}
		path, ok := single(r.model.objects("is_the_sqlite_file", store))
		if !allowed || !ok {
			continue
		}
		var kinds []string
		for _, k := range r.model.objects("keeps", store) {
			kinds = append(kinds, k.words())
		}
		sort.Strings(kinds)
		if err := r.writeStore(path.words(), kinds, answer); err != nil {
			r.problem(store.words() + " cannot be written: " + err.Error())
		}
	}
}

func (r *runner) writeStore(path string, kinds []string, answer string) error {
	temp := path + ".new"
	os.Remove(temp)
	db, err := sql.Open("sqlite", temp)
	if err != nil {
		return err
	}
	err = r.fillStore(db, kinds, answer)
	if cerr := db.Close(); err == nil {
		err = cerr
	}
	if err != nil {
		os.Remove(temp)
		return err
	}
	return os.Rename(temp, path)
}

func (r *runner) fillStore(db *sql.DB, kinds []string, answer string) error {
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	defer tx.Rollback()
	do := func(query string, args ...any) {
		if err == nil {
			_, err = tx.Exec(query, args...)
		}
	}
	facts := r.model.sorted()
	for _, kind := range kinds {
		switch kind {
		case rulesKind:
			do(`create table rules (id text, rule text, file text, line integer, text text)`)
			for _, s := range r.statements {
				do(`insert into rules values (?, ?, ?, ?, ?)`, s.id(), s.name(), s.file, s.line, strings.Join(s.lines, "\n"))
			}
		case factsKind:
			do(`create table facts (id text, fact text)`)
			for _, f := range facts {
				do(`insert into facts values (?, ?)`, shortHash(f.plain()), f.plain())
			}
		case reasonsKind:
			do(`create table reasons (fact_id text, fact text, rule text, rule_id text, premise_id text, premise text)`)
			for _, f := range facts {
				byRule := r.reasonsBy(f)
				var rules []*statement
				for s := range byRule {
					rules = append(rules, s)
				}
				sort.Slice(rules, func(i, j int) bool { return rules[i].name() < rules[j].name() })
				for _, s := range rules {
					for _, premises := range byRule[s] {
						if len(premises) == 0 {
							do(`insert into reasons values (?, ?, ?, ?, NULL, NULL)`, shortHash(f.plain()), f.plain(), s.name(), s.id())
						}
						for _, p := range premises {
							do(`insert into reasons values (?, ?, ?, ?, ?, ?)`, shortHash(f.plain()), f.plain(), s.name(), s.id(), shortHash(p.plain()), p.plain())
						}
					}
				}
			}
		case certificate:
			do(`create table certificate (part text, name text, value text)`)
			for _, part := range r.model.objects("holds", text(certificate)) {
				switch part.words() {
				case hashesPart:
					for _, file := range r.loaded {
						if data, ok := r.contents[file]; ok {
							sum := sha256.Sum256(data)
							do(`insert into certificate values (?, ?, ?)`, hashesPart, file, hex.EncodeToString(sum[:]))
						}
					}
				case answerPart:
					do(`insert into certificate values (?, ?, ?)`, answerPart, "", answer)
				}
			}
		}
	}
	if err != nil {
		return err
	}
	return tx.Commit()
}

func (r *runner) print(answer string) {
	me := text(engineFile)
	var places []string
	for _, v := range r.model.objects("prints_to", me) {
		places = append(places, v.words())
	}
	sort.Strings(places)
	for _, view := range r.model.objects("prints", me) {
		if view.words() != knowledgeView {
			continue
		}
		out := r.render(view.words())
		for _, place := range places {
			switch place {
			case "standard output":
				os.Stdout.WriteString(out)
			case "standard error":
				os.Stderr.WriteString(out)
			}
		}
	}
}

func run() int {
	r := &runner{
		change: os.Getenv(changeVariable) != "",
		loaded: []string{firstFile},
		done:   map[string]bool{},
	}
	for round := 0; ; round++ {
		more, err := r.step()
		if err != nil {
			r.problem("the knowledge cannot be evaluated: " + err.Error())
			break
		}
		if !more {
			break
		}
		if round == 100 {
			r.problem("the knowledge did not settle after 100 rounds")
			break
		}
	}
	r.checkTranslations()
	r.checkMachine()
	r.checkInstructions()
	r.giveReasons()
	answer, code := r.answer()
	r.publish(answer)
	if len(r.model.get("a_problem", 1)) > 0 && answer != "broken" {
		answer = "broken"
		if c, ok := r.exitCode(answer); ok {
			code = c
		} else {
			code = 2
		}
	}
	r.print(answer)
	return code
}

func main() {
	os.Exit(run())
}
