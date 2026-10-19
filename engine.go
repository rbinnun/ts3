package main

import (
	"bytes"
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/google/mangle/analysis"
	"github.com/google/mangle/ast"
	mangleengine "github.com/google/mangle/engine"
	"github.com/google/mangle/factstore"
	"github.com/google/mangle/parse"
	_ "modernc.org/sqlite"
)

const (
	engineFile     = "engine.go"
	changeVariable = "THIS_RUN_IS_A_CHANGE"
	plainKind      = "rules and facts"
	rowsKind       = "a row per line with a cell per column"
	printLanguage  = "plain language"
	whyPrefix      = "why__"
	maxRounds      = 32
)

var (
	blankPattern  = regexp.MustCompile(`^\[([^\[\]]+)\]$`)
	numberPattern = regexp.MustCompile(`^-?(0|[1-9][0-9]*)$`)
	phrasePattern = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
)

var knownMethods = map[string]string{
	"a rule id":       "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":       "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a derivation id": "the first 16 hex digits of the sha256 of the fact and the rule name and the reasons as plain lines joined by newlines",
	"a row name":      "the file name and a colon and the line number",
	"a cell value":    "the cell text read as a plain value",
}

var rowMeanings = map[string][]string{
	"every rule":                       {"the rule id", "the rule name", "the file the rule is in", "the number of the line the rule starts on", "the rule lines joined by newlines"},
	"every fact":                       {"the fact id", "the fact as one plain line", "the file that creates the predicate of the fact"},
	"every way a rule derives a fact":  {"the derivation id", "the fact id", "the rule name"},
	"every reason of every derivation": {"the derivation id", "the number of the condition in the rule", "the condition with its blanks filled as one plain line"},
	"every part the certificate holds": {"what the certificate holds", "the file a hash is of and empty for the answer", "the sha256 of the file in hex or the answer"},
}

const (
	hashPart   = "the hash of every file engine.go loads"
	answerPart = "the answer"
)

type Value struct {
	Num bool
	N   int64
	S   string
}

func text(s string) Value  { return Value{S: s} }
func number(n int64) Value { return Value{Num: true, N: n} }
func (v Value) key() string {
	if v.Num {
		return "n" + strconv.FormatInt(v.N, 10)
	}
	return "s" + v.S
}

func (v Value) plain() string {
	if v.Num {
		return strconv.FormatInt(v.N, 10)
	}
	return v.S
}

func plainValue(s string) Value {
	if numberPattern.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return number(n)
		}
	}
	return text(s)
}

type Term struct {
	Blank string
	Val   Value
}

type Atom struct {
	Pred   string
	IsForm bool
	Args   []Term
}

type Cond struct {
	Neg  bool
	Atom Atom
}

type Rule struct {
	Name    string
	File    string
	Line    int
	Order   int
	Lines   []string
	Head    Atom
	Conds   []Cond
	Bad     bool
	Clause  string
	WhyName string
	WhyVars []string
}

type Fact struct {
	Pred string
	Args []Value
}

func (f Fact) key() string {
	parts := []string{f.Pred}
	for _, a := range f.Args {
		parts = append(parts, a.key())
	}
	return strings.Join(parts, "\x00")
}

type predInfo struct {
	IsForm bool
	Arity  int
}

type template struct {
	params []string
	text   string
}

type creation struct {
	file string
	fact Fact
}

type Derivation struct {
	ID      string
	Fact    Fact
	Line    string
	Rule    *Rule
	Reasons []string
}

type Model struct {
	facts map[string][]Fact
	all   []Fact
	why   map[string][][]Value
}

type tablePlan struct {
	name    string
	kind    string
	columns []columnPlan
}

type columnPlan struct {
	position int64
	name     string
	meaning  string
}

type storePlan struct {
	path     string
	tables   []tablePlan
	onlyWhen []string
}

type Engine struct {
	mu          sync.Mutex
	entry       string
	rules       []*Rule
	contents    map[string][]byte
	problems    []string
	problemSeen map[string]bool
	preds       map[string]predInfo
	predWhere   map[string]string
	templates   map[string]template
	declared    map[string]map[string]bool
	creations   []creation
	createdSeen map[string]bool
	clauses     []ast.Clause
	patternPred map[string]string
	positions   map[string]int
	derivations []Derivation
	derivedBy   map[string][]int
	reasonsFor  map[string][]Fact
}

func newEngine(entry string) *Engine {
	return &Engine{
		entry:       entry,
		contents:    map[string][]byte{},
		problemSeen: map[string]bool{},
		preds:       map[string]predInfo{},
		predWhere:   map[string]string{},
		templates:   map[string]template{},
		declared:    map[string]map[string]bool{},
		createdSeen: map[string]bool{},
		patternPred: map[string]string{},
		positions:   map[string]int{},
		derivedBy:   map[string][]int{},
		reasonsFor:  map[string][]Fact{},
	}
}

func (e *Engine) problem(format string, args ...any) {
	p := strings.Join(strings.Fields(fmt.Sprintf(format, args...)), " ")
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.problemSeen[p] {
		return
	}
	e.problemSeen[p] = true
	e.problems = append(e.problems, p)
}

func (e *Engine) create(file, pred string, args ...Value) {
	f := Fact{Pred: pred, Args: args}
	k := file + "\x01" + f.key()
	if e.createdSeen[k] {
		return
	}
	e.createdSeen[k] = true
	e.creations = append(e.creations, creation{file, f})
}

func splitParts(s string) ([]string, error) {
	var parts []string
	for {
		if s == "" {
			return nil, errors.New("a part is empty")
		}
		if s[0] == '"' || s[0] == '\'' {
			end := strings.IndexByte(s[1:], s[0])
			if end < 0 {
				return nil, errors.New("a quote is not closed")
			}
			parts = append(parts, s[:end+2])
			s = s[end+2:]
			if s == "" {
				return parts, nil
			}
			if !strings.HasPrefix(s, ", ") {
				return nil, errors.New("a quote is followed by more than a comma")
			}
			s = s[2:]
			continue
		}
		k := strings.Index(s, ", ")
		if k < 0 {
			return append(parts, s), nil
		}
		parts = append(parts, s[:k])
		s = s[k+2:]
	}
}

func parsePart(raw string) (Term, bool, error) {
	if raw == "" {
		return Term{}, false, errors.New("a part is empty")
	}
	if raw[0] == '"' || raw[0] == '\'' {
		return Term{Val: text(raw[1 : len(raw)-1])}, false, nil
	}
	if m := blankPattern.FindStringSubmatch(raw); m != nil {
		if !phrasePattern.MatchString(m[1]) {
			return Term{}, false, fmt.Errorf("the blank %s is not made of lowercase words", raw)
		}
		return Term{Blank: m[1]}, false, nil
	}
	return Term{Val: plainValue(raw)}, true, nil
}

func parseStatement(s string) (Atom, error) {
	raws, err := splitParts(s)
	if err != nil {
		return Atom{}, err
	}
	terms := make([]Term, len(raws))
	bare := make([]bool, len(raws))
	for i, raw := range raws {
		t, b, err := parsePart(raw)
		if err != nil {
			return Atom{}, err
		}
		terms[i], bare[i] = t, b
	}
	word := func(i int) (string, bool) {
		if !bare[i] || terms[i].Val.Num {
			return "", false
		}
		return terms[i].Val.S, true
	}
	switch len(terms) {
	case 1:
		w, ok := word(0)
		if !ok || !phrasePattern.MatchString(w) {
			return Atom{}, errors.New("a line with one part must be lowercase words")
		}
		return Atom{Pred: w}, nil
	case 2:
		return Atom{}, errors.New("a line has two parts, but it needs one part or three or more")
	}
	verb, ok := word(1)
	if !ok || !phrasePattern.MatchString(verb) {
		return Atom{}, errors.New("the second part of a line must be lowercase words")
	}
	if verb == "is" && len(terms) == 3 {
		if w, ok := word(2); ok {
			if !phrasePattern.MatchString(w) {
				return Atom{}, errors.New("what follows is must be lowercase words")
			}
			return Atom{Pred: w, IsForm: true, Args: terms[:1]}, nil
		}
	}
	args := append([]Term{terms[0]}, terms[2:]...)
	return Atom{Pred: verb, Args: args}, nil
}

func quote(s string) string {
	if !strings.Contains(s, `"`) {
		return `"` + s + `"`
	}
	if !strings.Contains(s, "'") {
		return "'" + s + "'"
	}
	return `"` + s + `"`
}

func bareSafe(s string) bool {
	return s != "" && strings.TrimSpace(s) == s && s[0] != '"' && s[0] != '\'' &&
		!strings.Contains(s, ", ") && !strings.ContainsAny(s, "\r\n") &&
		!blankPattern.MatchString(s) && !numberPattern.MatchString(s)
}

func renderValue(v Value) string {
	if v.Num {
		return strconv.FormatInt(v.N, 10)
	}
	if bareSafe(v.S) {
		return v.S
	}
	return quote(v.S)
}

func renderTerm(t Term) string {
	if t.Blank != "" {
		return "[" + t.Blank + "]"
	}
	return renderValue(t.Val)
}

func renderAtom(a Atom, condition bool) string {
	if len(a.Args) == 0 {
		return a.Pred
	}
	first := renderTerm(a.Args[0])
	if condition && a.Args[0].Blank == "" && !a.Args[0].Val.Num && strings.HasPrefix(first, "not ") {
		first = quote(a.Args[0].Val.S)
	}
	if a.IsForm {
		return first + ", is, " + a.Pred
	}
	parts := []string{first, a.Pred}
	for _, t := range a.Args[1:] {
		parts = append(parts, renderTerm(t))
	}
	return strings.Join(parts, ", ")
}

func renderCond(c Cond) string {
	s := renderAtom(c.Atom, true)
	if c.Neg {
		return "not " + s
	}
	return s
}

func renderRule(r *Rule) []string {
	lines := []string{renderAtom(r.Head, false)}
	for i, c := range r.Conds {
		lead := "    and "
		if i == 0 {
			lead = "    if "
		}
		lines = append(lines, lead+renderCond(c))
	}
	return lines
}

func parsePlainText(file, content string) ([]*Rule, []string) {
	var rules []*Rule
	var problems []string
	lines := strings.Split(content, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var cur *Rule
	for i, line := range lines {
		n := i + 1
		if strings.TrimSpace(line) == "" {
			cur = nil
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			if cur == nil {
				problems = append(problems, fmt.Sprintf("%s:%d is a condition without a rule", file, n))
				continue
			}
			cur.Lines = append(cur.Lines, line)
			if cur.Bad {
				continue
			}
			t := strings.TrimLeft(line, " \t")
			var body string
			switch {
			case strings.HasPrefix(t, "if "):
				body = t[3:]
			case strings.HasPrefix(t, "and "):
				body = t[4:]
			default:
				problems = append(problems, fmt.Sprintf("%s:%d is indented but does not start with if or and", file, n))
				cur.Bad = true
				continue
			}
			neg := false
			if strings.HasPrefix(body, "not ") {
				neg, body = true, body[4:]
			}
			a, err := parseStatement(body)
			if err != nil {
				problems = append(problems, fmt.Sprintf("%s:%d cannot be read: %v", file, n, err))
				cur.Bad = true
				continue
			}
			cur.Conds = append(cur.Conds, Cond{Neg: neg, Atom: a})
			continue
		}
		cur = &Rule{Name: fmt.Sprintf("%s:%d", file, n), File: file, Line: n, Lines: []string{line}}
		rules = append(rules, cur)
		a, err := parseStatement(line)
		if err != nil {
			problems = append(problems, fmt.Sprintf("%s:%d cannot be read: %v", file, n, err))
			cur.Bad = true
			continue
		}
		cur.Head = a
	}
	return rules, problems
}

func groundFact(a Atom) (Fact, bool) {
	f := Fact{Pred: a.Pred}
	for _, t := range a.Args {
		if t.Blank != "" {
			return Fact{}, false
		}
		f.Args = append(f.Args, t.Val)
	}
	return f, true
}

func hasBlanks(a Atom) bool {
	for _, t := range a.Args {
		if t.Blank != "" {
			return true
		}
	}
	return false
}

func (e *Engine) groundFacts(pred string) []Fact {
	var out []Fact
	for _, r := range e.rules {
		if r.Bad || len(r.Conds) > 0 || r.Head.Pred != pred {
			continue
		}
		if f, ok := groundFact(r.Head); ok {
			out = append(out, f)
		}
	}
	return out
}

func (e *Engine) factsOf(m *Model, pred string) []Fact {
	if m != nil {
		return m.facts[pred]
	}
	return e.groundFacts(pred)
}

func (e *Engine) load() {
	queue := []string{e.entry}
	seen := map[string]bool{}
	for len(queue) > 0 {
		name := queue[0]
		queue = queue[1:]
		if seen[name] {
			continue
		}
		seen[name] = true
		data, err := os.ReadFile(name)
		if err != nil {
			if !errors.Is(err, os.ErrNotExist) {
				e.problem("engine.go cannot read %s: %v", name, err)
			}
			continue
		}
		kind := plainKind
		if name != e.entry {
			kind = e.kindOf(name)
		}
		switch kind {
		case plainKind:
			e.loadPlain(name, string(data))
		case rowsKind:
			e.loadRows(name, data)
		case "":
			continue
		default:
			e.problem("engine.go does not know how to load %s as %s", name, kind)
			continue
		}
		e.contents[name] = data
		for _, f := range e.groundFacts("loads") {
			if len(f.Args) == 2 && f.Args[0] == text(engineFile) && !f.Args[1].Num && !seen[f.Args[1].S] {
				queue = append(queue, f.Args[1].S)
			}
		}
	}
	if _, ok := e.contents[e.entry]; ok {
		if kind := e.kindOf(e.entry); kind != "" && kind != plainKind {
			e.problem("engine.go starts from %s as %s, but it is loaded as %s", e.entry, plainKind, kind)
		}
	}
}

func (e *Engine) kindOf(name string) string {
	best, language := "", ""
	for _, f := range e.groundFacts("means") {
		if len(f.Args) != 2 || f.Args[0].Num || f.Args[1].Num {
			continue
		}
		ending := f.Args[0].S
		if ending != "" && strings.HasSuffix(name, ending) && len(ending) > len(best) {
			best, language = ending, f.Args[1].S
		}
	}
	if language == "" {
		e.problem("engine.go does not know the language of %s", name)
		return ""
	}
	var kinds []string
	for _, f := range e.groundFacts("is loaded as") {
		if len(f.Args) == 2 && f.Args[0] == text(language) && !f.Args[1].Num {
			kinds = append(kinds, f.Args[1].S)
		}
	}
	if len(kinds) != 1 {
		e.problem("engine.go does not know how %s is loaded", language)
		return ""
	}
	return kinds[0]
}

func (e *Engine) loadPlain(name, content string) {
	rules, problems := parsePlainText(name, content)
	for _, p := range problems {
		e.problem("%s", p)
	}
	for _, r := range rules {
		r.Order = len(e.rules)
		e.rules = append(e.rules, r)
		if r.Bad || len(r.Conds) > 0 {
			continue
		}
		if f, ok := groundFact(r.Head); ok {
			if _, seen := e.positions[f.key()]; !seen {
				e.positions[f.key()] = r.Order
			}
		}
	}
}

func (e *Engine) loadRows(name string, data []byte) {
	r := csv.NewReader(bytes.NewReader(data))
	r.FieldsPerRecord = -1
	header, err := r.Read()
	if err == io.EOF {
		return
	}
	if err != nil {
		e.problem("%s cannot be read: %v", name, err)
		return
	}
	for {
		record, err := r.Read()
		if err == io.EOF {
			return
		}
		if err != nil {
			e.problem("%s cannot be read: %v", name, err)
			return
		}
		line, _ := r.FieldPos(0)
		row := text(fmt.Sprintf("%s:%d", name, line))
		if len(record) != len(header) {
			e.problem("%s:%d has %d cells, but the first line names %d columns", name, line, len(record), len(header))
		}
		e.create(engineFile, "is a row of", row, text(name))
		e.create(engineFile, "is on line", row, number(int64(line)))
		for i, cell := range record {
			if i < len(header) {
				e.create(engineFile, "has the cell", row, text(header[i]), plainValue(cell))
			}
		}
	}
}

func mangleName(phrase string) string {
	return strings.ReplaceAll(phrase, " ", "_")
}

func varName(blank string) string {
	var b strings.Builder
	for _, w := range strings.Fields(blank) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	return b.String()
}

func mangleString(s string) string {
	r := strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`, "\t", `\t`)
	return `"` + r.Replace(s) + `"`
}

func mangleTerm(t Term) string {
	if t.Blank != "" {
		return varName(t.Blank)
	}
	if t.Val.Num {
		return strconv.FormatInt(t.Val.N, 10)
	}
	return mangleString(t.Val.S)
}

func regularMangle(a Atom) string {
	args := make([]string, len(a.Args))
	for i, t := range a.Args {
		args[i] = mangleTerm(t)
	}
	return mangleName(a.Pred) + "(" + strings.Join(args, ", ") + ")"
}

func isIdentByte(c byte) bool {
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

func instantiate(t template, args []Term) string {
	repl := map[string]string{}
	for i, p := range t.params {
		repl[p] = mangleTerm(args[i])
	}
	s := t.text
	var b strings.Builder
	for i := 0; i < len(s); {
		c := s[i]
		if c == '"' || c == '\'' {
			j := i + 1
			for j < len(s) && s[j] != c {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			if j < len(s) {
				j++
			}
			if j > len(s) {
				j = len(s)
			}
			b.WriteString(s[i:j])
			i = j
			continue
		}
		if isIdentByte(c) {
			j := i
			for j < len(s) && isIdentByte(s[j]) {
				j++
			}
			word := s[i:j]
			if r, ok := repl[word]; ok && (i == 0 || s[i-1] != ':') {
				b.WriteString(r)
			} else {
				b.WriteString(word)
			}
			i = j
			continue
		}
		b.WriteByte(c)
		i++
	}
	return b.String()
}

func (e *Engine) isBuiltin(a Atom) bool {
	_, ok := e.templates[a.Pred]
	return ok && !a.IsForm
}

func (e *Engine) mangleAtom(a Atom) (string, bool, error) {
	if t, ok := e.templates[a.Pred]; ok && !a.IsForm {
		if len(t.params) != len(a.Args) {
			return "", true, fmt.Errorf("%s needs %d parts besides itself", a.Pred, len(t.params))
		}
		return instantiate(t, a.Args), true, nil
	}
	return regularMangle(a), false, nil
}

func (e *Engine) mangleLine(a Atom) (string, error) {
	s, builtin, err := e.mangleAtom(a)
	if err != nil {
		return "", err
	}
	if builtin {
		return s, nil
	}
	return s + ".", nil
}

func templateLine(a Atom) bool {
	if a.IsForm || len(a.Args) < 2 {
		return false
	}
	seen := map[string]bool{}
	for _, t := range a.Args {
		if t.Blank == "" || seen[t.Blank] {
			return false
		}
		seen[t.Blank] = true
	}
	return true
}

func (e *Engine) learnTemplates() {
	type pair struct {
		atom   Atom
		line   string
		mangle string
	}
	var pairs []pair
	for _, f := range e.groundFacts("means in mangle") {
		if len(f.Args) != 2 || f.Args[0].Num || f.Args[1].Num {
			continue
		}
		a, err := parseStatement(f.Args[0].S)
		if err != nil {
			e.problem("the line %s cannot be read: %v", f.Args[0].S, err)
			continue
		}
		pairs = append(pairs, pair{a, f.Args[0].S, f.Args[1].S})
	}
	for _, p := range pairs {
		if regularMangle(p.atom)+"." == p.mangle || !templateLine(p.atom) {
			continue
		}
		params := make([]string, len(p.atom.Args))
		for i, t := range p.atom.Args {
			params[i] = varName(t.Blank)
		}
		if old, ok := e.templates[p.atom.Pred]; ok {
			if old.text != p.mangle || strings.Join(old.params, ",") != strings.Join(params, ",") {
				e.problem("%s means two different things in mangle", p.atom.Pred)
			}
			continue
		}
		e.templates[p.atom.Pred] = template{params, p.mangle}
	}
	for _, p := range pairs {
		got, err := e.mangleLine(p.atom)
		if err != nil {
			e.problem("the line %s cannot be read as mangle: %v", p.line, err)
			continue
		}
		if got != p.mangle {
			e.problem("engine.go reads the line %s as %s in mangle, not as %s", p.line, got, p.mangle)
		}
	}
}

func parsePattern(p string) (string, bool, []string, error) {
	type token struct {
		blank bool
		s     string
	}
	var toks []token
	rest := p
	for rest != "" {
		if rest[0] == '[' {
			j := strings.IndexByte(rest, ']')
			if j < 0 {
				return "", false, nil, errors.New("a blank is not closed")
			}
			toks = append(toks, token{true, rest[1:j]})
			rest = rest[j+1:]
			continue
		}
		j := strings.IndexByte(rest, '[')
		if j < 0 {
			j = len(rest)
		}
		if w := strings.TrimSpace(rest[:j]); w != "" {
			toks = append(toks, token{false, w})
		}
		rest = rest[j:]
	}
	if len(toks) == 1 && !toks[0].blank {
		if !phrasePattern.MatchString(toks[0].s) {
			return "", false, nil, errors.New("its words are not lowercase words")
		}
		return toks[0].s, false, nil, nil
	}
	if len(toks) < 2 || !toks[0].blank || toks[1].blank {
		return "", false, nil, errors.New("it must start with a blank and then words")
	}
	slots := []string{toks[0].s}
	for _, t := range toks[2:] {
		if !t.blank {
			return "", false, nil, errors.New("words may only follow the first blank")
		}
		slots = append(slots, t.s)
	}
	verb := toks[1].s
	if !phrasePattern.MatchString(verb) {
		return "", false, nil, errors.New("its words are not lowercase words")
	}
	for _, s := range slots {
		if !phrasePattern.MatchString(s) {
			return "", false, nil, fmt.Errorf("the blank [%s] is not made of lowercase words", s)
		}
	}
	if len(slots) == 1 && strings.HasPrefix(verb, "is ") {
		return verb[3:], true, slots, nil
	}
	return verb, false, slots, nil
}

func (e *Engine) register(pred string, isForm bool, arity int, where string) {
	if old, ok := e.preds[pred]; ok {
		if old.IsForm != isForm || old.Arity != arity {
			e.problem("%s uses %s in another shape than %s does", where, pred, e.predWhere[pred])
		}
		return
	}
	e.preds[pred] = predInfo{IsForm: isForm, Arity: arity}
	e.predWhere[pred] = where
}

func (e *Engine) readPatterns() {
	for _, holder := range []string{"executes instruction", "creates fact", "shows", "gives reasons for"} {
		for _, f := range e.groundFacts(holder) {
			if len(f.Args) != 2 || f.Args[1].Num {
				continue
			}
			pattern := f.Args[1].S
			pred, isForm, slots, err := parsePattern(pattern)
			if err != nil {
				e.problem("the fact pattern %s cannot be read: %v", pattern, err)
				continue
			}
			if holder == "creates fact" && !f.Args[0].Num {
				if e.declared[f.Args[0].S] == nil {
					e.declared[f.Args[0].S] = map[string]bool{}
				}
				e.declared[f.Args[0].S][pred] = true
			}
			if _, done := e.patternPred[pattern]; done {
				continue
			}
			e.patternPred[pattern] = pred
			e.register(pred, isForm, len(slots), "the fact pattern "+pattern)
			e.create(engineFile, "names", text(pattern), text(pred))
			for _, s := range slots {
				e.create(engineFile, "has the slot", text(pattern), text(s))
			}
		}
	}
}

func sha16(s string) string {
	h := sha256.Sum256([]byte(s))
	return hex.EncodeToString(h[:])[:16]
}

func (e *Engine) prepare() {
	e.learnTemplates()
	e.readPatterns()
	if os.Getenv(changeVariable) != "" {
		e.create(engineFile, "this run is a change")
	}
	for _, r := range e.rules {
		if r.Bad {
			continue
		}
		e.registerRule(r)
		e.syntaxFacts(r)
		e.translate(r)
	}
}

func (e *Engine) registerRule(r *Rule) {
	atoms := []Atom{r.Head}
	for _, c := range r.Conds {
		atoms = append(atoms, c.Atom)
	}
	for _, a := range atoms {
		if !e.isBuiltin(a) {
			e.register(a.Pred, a.IsForm, len(a.Args), r.Name)
		}
	}
}

func (e *Engine) syntaxFacts(r *Rule) {
	name := text(r.Name)
	e.create(engineFile, "has the id", name, text(sha16(strings.Join(r.Lines, "\n"))))
	if strings.Join(renderRule(r), "\n") != strings.Join(r.Lines, "\n") {
		e.create(engineFile, "read back differently", name)
	}
	e.create(engineFile, "has a rule for", text(r.File), text(r.Head.Pred))
	e.create(engineFile, "defines", name, text(r.Head.Pred))
	for _, c := range r.Conds {
		if !e.isBuiltin(c.Atom) {
			e.create(engineFile, "refers to", name, text(c.Atom.Pred))
		}
	}
	if r.Head.Pred == "breaks" && !r.Head.IsForm && len(r.Head.Args) == 2 && r.Head.Args[1].Blank == "" {
		e.create(engineFile, "lays down", name, r.Head.Args[1].Val)
	}
	atoms := []Atom{r.Head}
	for _, c := range r.Conds {
		atoms = append(atoms, c.Atom)
	}
	for _, a := range atoms {
		for _, t := range a.Args {
			if t.Blank != "" {
				e.create(engineFile, "has the blank", name, text(t.Blank))
			}
		}
	}
}

func (e *Engine) translate(r *Rule) {
	head, builtin, err := e.mangleAtom(r.Head)
	if err == nil && builtin {
		err = errors.New("its first line is built in, so it cannot be concluded")
	}
	if err == nil && len(r.Conds) == 0 && hasBlanks(r.Head) {
		err = errors.New("a fact cannot have blanks")
	}
	var premises []string
	for _, c := range r.Conds {
		if err != nil {
			break
		}
		var t string
		var b bool
		t, b, err = e.mangleAtom(c.Atom)
		if err == nil && c.Neg {
			if b {
				err = errors.New("a built-in condition cannot be negated")
			}
			t = "!" + t
		}
		premises = append(premises, t)
	}
	if err != nil {
		e.problem("%s cannot be read as mangle: %v", r.Name, err)
		return
	}
	source := head + "."
	if len(premises) > 0 {
		source = head + " :- " + strings.Join(premises, ", ") + "."
	}
	clause, err := parse.Clause(source)
	if err != nil {
		e.problem("%s cannot be read as mangle: %v", r.Name, err)
		return
	}
	if _, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: []ast.Clause{clause}}, e.extraDecls(map[ast.PredicateSym]bool{clause.Head.Predicate: true})); err != nil {
		e.problem("%s cannot be read as mangle: %v", r.Name, err)
		return
	}
	e.clauses = append(e.clauses, clause)
	r.Clause = source
	if len(r.Conds) == 0 {
		return
	}
	seen := map[string]bool{}
	var vars, names []string
	for _, c := range r.Conds {
		if c.Neg {
			continue
		}
		for _, t := range c.Atom.Args {
			if t.Blank != "" && !seen[t.Blank] {
				seen[t.Blank] = true
				vars = append(vars, t.Blank)
				names = append(names, varName(t.Blank))
			}
		}
	}
	whyName := fmt.Sprintf("%s%d", whyPrefix, r.Order)
	why, err := parse.Clause(whyName + "(" + strings.Join(names, ", ") + ") :- " + strings.Join(premises, ", ") + ".")
	if err != nil {
		e.problem("the reasons of %s cannot be read as mangle: %v", r.Name, err)
		return
	}
	e.clauses = append(e.clauses, why)
	r.WhyName, r.WhyVars = whyName, vars
}

func (e *Engine) extraDecls(heads map[ast.PredicateSym]bool) map[ast.PredicateSym]ast.Decl {
	extra := map[ast.PredicateSym]ast.Decl{}
	for pred, info := range e.preds {
		sym := ast.PredicateSym{Symbol: mangleName(pred), Arity: info.Arity}
		if !heads[sym] {
			extra[sym] = ast.NewSyntheticDeclFromSym(sym)
		}
	}
	return extra
}

func mangleFact(f Fact) ast.Atom {
	args := make([]ast.BaseTerm, len(f.Args))
	for i, v := range f.Args {
		if v.Num {
			args[i] = ast.Number(v.N)
		} else {
			args[i] = ast.String(v.S)
		}
	}
	return ast.NewAtom(mangleName(f.Pred), args...)
}

func fromConstant(t ast.BaseTerm) Value {
	c, ok := t.(ast.Constant)
	if !ok {
		return text(t.String())
	}
	switch c.Type {
	case ast.StringType:
		return text(c.Symbol)
	case ast.NumberType:
		return number(c.NumValue)
	}
	return text(c.String())
}

func (e *Engine) evaluate() (*Model, error) {
	clauses := make([]ast.Clause, 0, len(e.clauses)+len(e.creations))
	clauses = append(clauses, e.clauses...)
	for _, c := range e.creations {
		clauses = append(clauses, ast.Clause{Head: mangleFact(c.fact)})
	}
	heads := map[ast.PredicateSym]bool{}
	for _, c := range clauses {
		heads[c.Head.Predicate] = true
	}
	info, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: clauses}, e.extraDecls(heads))
	if err != nil {
		return nil, err
	}
	store := factstore.NewSimpleInMemoryStore()
	if err := mangleengine.EvalProgram(info, store); err != nil {
		return nil, err
	}
	m := &Model{facts: map[string][]Fact{}, why: map[string][][]Value{}}
	for _, sym := range store.ListPredicates() {
		symbol := sym.Symbol
		err := store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			vals := make([]Value, len(a.Args))
			for i, t := range a.Args {
				vals[i] = fromConstant(t)
			}
			if strings.HasPrefix(symbol, whyPrefix) {
				m.why[symbol] = append(m.why[symbol], vals)
				return nil
			}
			f := Fact{Pred: strings.ReplaceAll(symbol, "_", " "), Args: vals}
			m.facts[f.Pred] = append(m.facts[f.Pred], f)
			m.all = append(m.all, f)
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	return m, nil
}

func (e *Engine) solve() *Model {
	called := map[string]bool{}
	for round := 0; round < maxRounds; round++ {
		m, err := e.evaluate()
		if err != nil {
			e.problem("the knowledge cannot be evaluated: %v", err)
			return nil
		}
		var calls []Call
		for _, f := range m.facts["calls"] {
			if len(f.Args) != 3 || called[f.key()] {
				continue
			}
			called[f.key()] = true
			calls = append(calls, Call{Command: f.Args[0], Tool: f.Args[1], Input: f.Args[2]})
		}
		if len(calls) == 0 {
			return m
		}
		sort.Slice(calls, func(i, j int) bool {
			return lessValues([]Value{calls[i].Command, calls[i].Tool, calls[i].Input}, []Value{calls[j].Command, calls[j].Tool, calls[j].Input})
		})
		e.callTools(calls, m)
	}
	e.problem("the commands still change after %d rounds", maxRounds)
	return nil
}

func fill(a Atom, bind map[string]Value) Atom {
	out := Atom{Pred: a.Pred, IsForm: a.IsForm, Args: make([]Term, len(a.Args))}
	for i, t := range a.Args {
		if v, ok := bind[t.Blank]; ok && t.Blank != "" {
			out.Args[i] = Term{Val: v}
		} else {
			out.Args[i] = t
		}
	}
	return out
}

func (e *Engine) predShape(pred string, arity int) Atom {
	info, ok := e.preds[pred]
	return Atom{Pred: pred, IsForm: ok && info.IsForm && arity == 1}
}

func (e *Engine) line(f Fact) string {
	a := e.predShape(f.Pred, len(f.Args))
	for _, v := range f.Args {
		a.Args = append(a.Args, Term{Val: v})
	}
	return renderAtom(a, false)
}

func (e *Engine) derive(m *Model) {
	seen := map[string]bool{}
	add := func(f Fact, r *Rule, reasons []string) {
		line := e.line(f)
		id := sha16(strings.Join(append([]string{line, r.Name}, reasons...), "\n"))
		if seen[id] {
			return
		}
		seen[id] = true
		e.derivedBy[f.key()] = append(e.derivedBy[f.key()], len(e.derivations))
		e.derivations = append(e.derivations, Derivation{ID: id, Fact: f, Line: line, Rule: r, Reasons: reasons})
	}
	for _, r := range e.rules {
		if r.Bad || r.Clause == "" {
			continue
		}
		if len(r.Conds) == 0 {
			if f, ok := groundFact(r.Head); ok {
				add(f, r, nil)
			}
			continue
		}
		tuples := m.why[r.WhyName]
		sort.Slice(tuples, func(i, j int) bool { return lessValues(tuples[i], tuples[j]) })
		for _, tuple := range tuples {
			bind := map[string]Value{}
			for i, b := range r.WhyVars {
				if i < len(tuple) {
					bind[b] = tuple[i]
				}
			}
			f, ok := groundFact(fill(r.Head, bind))
			if !ok {
				continue
			}
			reasons := make([]string, len(r.Conds))
			for i, c := range r.Conds {
				reasons[i] = renderCond(Cond{Neg: c.Neg, Atom: fill(c.Atom, bind)})
			}
			add(f, r, reasons)
		}
	}
}

func (e *Engine) views(m *Model) []string {
	var out []string
	seen := map[string]bool{}
	for _, f := range e.factsOf(m, "prints") {
		if len(f.Args) == 2 && f.Args[0] == text(engineFile) && !f.Args[1].Num && !seen[f.Args[1].S] {
			seen[f.Args[1].S] = true
			out = append(out, f.Args[1].S)
		}
	}
	sort.Strings(out)
	return out
}

func (e *Engine) objects(m *Model, pred, subject string) []string {
	var out []string
	seen := map[string]bool{}
	for _, f := range e.factsOf(m, pred) {
		if len(f.Args) == 2 && f.Args[0] == text(subject) && !seen[f.Args[1].key()] {
			seen[f.Args[1].key()] = true
			out = append(out, f.Args[1].plain())
		}
	}
	sort.Strings(out)
	return out
}

func (e *Engine) explain(m *Model) {
	for _, view := range e.views(m) {
		for _, pattern := range e.objects(m, "gives reasons for", view) {
			pred, ok := e.patternPred[pattern]
			if !ok {
				e.problem("engine.go cannot give reasons for %s", pattern)
				continue
			}
			for _, f := range m.facts[pred] {
				line := e.line(f)
				if _, done := e.reasonsFor[line]; done {
					continue
				}
				seen := map[string]bool{}
				var hold []Fact
				for _, i := range e.derivedBy[f.key()] {
					for _, reason := range e.derivations[i].Reasons {
						if seen[reason] {
							continue
						}
						seen[reason] = true
						h := Fact{Pred: "holds because", Args: []Value{text(line), text(reason)}}
						e.create(engineFile, h.Pred, h.Args...)
						hold = append(hold, h)
					}
				}
				e.reasonsFor[line] = hold
			}
		}
	}
}

func (e *Engine) checkCreations() {
	for _, c := range e.creations {
		if !e.declared[c.file][c.fact.Pred] {
			e.problem("%s creates facts of %s, but nothing says it does", c.file, c.fact.Pred)
		}
	}
	if len(e.problems) > 0 && !e.declared[engineFile]["a problem"] {
		e.problem("%s creates facts of %s, but nothing says it does", engineFile, "a problem")
	}
}

func (e *Engine) checkInstructions(m *Model) {
	for _, f := range m.facts["is computed as"] {
		if len(f.Args) != 2 {
			continue
		}
		kind, method := f.Args[0].plain(), f.Args[1].plain()
		known, ok := knownMethods[kind]
		if !ok {
			e.problem("engine.go does not compute %s", kind)
		} else if known != method {
			e.problem("engine.go computes %s as %s, not as %s", kind, known, method)
		}
	}
	for _, f := range m.facts["is loaded as"] {
		if len(f.Args) == 2 && f.Args[1] != text(plainKind) && f.Args[1] != text(rowsKind) {
			e.problem("engine.go cannot load anything as %s", f.Args[1].plain())
		}
	}
	for _, language := range e.objects(m, "prints in", engineFile) {
		if language != printLanguage {
			e.problem("engine.go cannot print in %s", language)
		}
	}
	for _, place := range e.objects(m, "prints to", engineFile) {
		if place != "standard output" && place != "standard error" {
			e.problem("engine.go cannot print to %s", place)
		}
	}
}

func (e *Engine) plans(m *Model) []storePlan {
	var plans []storePlan
	for _, view := range e.views(m) {
		for _, store := range e.objects(m, "is published to", view) {
			paths := e.objects(m, "is the sqlite file", store)
			if len(paths) != 1 {
				e.problem("%s must be exactly one sqlite file", store)
				continue
			}
			plan := storePlan{path: paths[0], onlyWhen: e.objects(m, "is published only when", view)}
			for _, table := range e.objects(m, "has the table", store) {
				kinds := e.objects(m, "has a row for", table)
				if len(kinds) != 1 {
					e.problem("the table %s must have a row for exactly one thing", table)
					continue
				}
				meanings, ok := rowMeanings[kinds[0]]
				if !ok {
					e.problem("engine.go cannot make a row for %s", kinds[0])
					continue
				}
				t := tablePlan{name: table, kind: kinds[0]}
				for _, f := range m.facts["has the column"] {
					if len(f.Args) != 4 || f.Args[0] != text(table) {
						continue
					}
					if !f.Args[1].Num {
						e.problem("the column %s of %s has no number", f.Args[2].plain(), table)
						continue
					}
					meaning := f.Args[3].plain()
					found := false
					for _, known := range meanings {
						found = found || known == meaning
					}
					if !found {
						e.problem("engine.go cannot fill a column of %s with %s", table, meaning)
						continue
					}
					t.columns = append(t.columns, columnPlan{f.Args[1].N, f.Args[2].plain(), meaning})
				}
				sort.Slice(t.columns, func(i, j int) bool { return t.columns[i].position < t.columns[j].position })
				for i := 1; i < len(t.columns); i++ {
					if t.columns[i].position == t.columns[i-1].position {
						e.problem("the table %s has two columns at %d", table, t.columns[i].position)
					}
				}
				plan.tables = append(plan.tables, t)
			}
			plans = append(plans, plan)
		}
	}
	for _, part := range e.objects(m, "holds", "the certificate") {
		if part != hashPart && part != answerPart {
			e.problem("engine.go cannot put %s in the certificate", part)
		}
	}
	return plans
}

func (e *Engine) answer(m *Model) string {
	if m == nil || len(e.problems) > 0 {
		return "broken"
	}
	seen := map[string]bool{}
	var answers []string
	for _, f := range m.facts["conforms"] {
		if len(f.Args) == 2 && !seen[f.Args[1].key()] {
			seen[f.Args[1].key()] = true
			answers = append(answers, f.Args[1].plain())
		}
	}
	if len(answers) != 1 {
		e.problem("the folder conforms with %d answers instead of one", len(answers))
		return "broken"
	}
	return answers[0]
}

func (e *Engine) exitCode(m *Model, answer string) (int, bool) {
	for _, f := range e.factsOf(m, "exits with") {
		if len(f.Args) == 2 && f.Args[0] == text(answer) && f.Args[1].Num {
			return int(f.Args[1].N), true
		}
	}
	return 0, false
}

func (e *Engine) decide(m *Model) (string, int) {
	answer := e.answer(m)
	code, ok := e.exitCode(m, answer)
	if !ok {
		e.problem("nothing says what %s exits with", answer)
		answer = "broken"
		if code, ok = e.exitCode(m, answer); !ok {
			code = 2
		}
	}
	return answer, code
}

func (e *Engine) knowledge(m *Model) []Fact {
	seen := map[string]bool{}
	var all []Fact
	add := func(f Fact) {
		if k := f.key(); !seen[k] {
			seen[k] = true
			all = append(all, f)
		}
	}
	if m != nil {
		for _, f := range m.all {
			add(f)
		}
	}
	for _, c := range e.creations {
		add(c.fact)
	}
	e.mu.Lock()
	for _, p := range e.problems {
		add(Fact{Pred: "a problem", Args: []Value{text(p)}})
	}
	e.mu.Unlock()
	return all
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func naturalCompare(a, b string) int {
	for a != "" && b != "" {
		if isDigit(a[0]) && isDigit(b[0]) {
			i, j := 0, 0
			for i < len(a) && isDigit(a[i]) {
				i++
			}
			for j < len(b) && isDigit(b[j]) {
				j++
			}
			na, nb := strings.TrimLeft(a[:i], "0"), strings.TrimLeft(b[:j], "0")
			if len(na) != len(nb) {
				if len(na) < len(nb) {
					return -1
				}
				return 1
			}
			if na != nb {
				if na < nb {
					return -1
				}
				return 1
			}
			a, b = a[i:], b[j:]
			continue
		}
		if a[0] != b[0] {
			if a[0] < b[0] {
				return -1
			}
			return 1
		}
		a, b = a[1:], b[1:]
	}
	return len(a) - len(b)
}

func compareValue(a, b Value) int {
	if a.Num && b.Num {
		switch {
		case a.N < b.N:
			return -1
		case a.N > b.N:
			return 1
		}
		return 0
	}
	if a.Num != b.Num {
		if a.Num {
			return -1
		}
		return 1
	}
	return naturalCompare(a.S, b.S)
}

func lessValues(a, b []Value) bool {
	for i := 0; i < len(a) && i < len(b); i++ {
		if c := compareValue(a[i], b[i]); c != 0 {
			return c < 0
		}
	}
	return len(a) < len(b)
}

func sortFacts(facts []Fact) []Fact {
	out := append([]Fact(nil), facts...)
	sort.SliceStable(out, func(i, j int) bool { return lessValues(out[i].Args, out[j].Args) })
	return out
}

func (e *Engine) render(m *Model, all []Fact) string {
	byPred := map[string][]Fact{}
	for _, f := range all {
		byPred[f.Pred] = append(byPred[f.Pred], f)
	}
	var b strings.Builder
	if m == nil {
		for _, f := range sortFacts(byPred["a problem"]) {
			b.WriteString(e.line(f) + "\n")
		}
		return b.String()
	}
	inView := map[string]bool{}
	for _, f := range m.facts["in the knowledge view"] {
		if len(f.Args) == 1 {
			inView[f.Args[0].plain()] = true
		}
	}
	first, prevLong := true, false
	for _, r := range e.rules {
		if r.Bad || !inView[r.Name] {
			continue
		}
		long := len(r.Lines) > 1
		if !first && (long || prevLong) {
			b.WriteString("\n")
		}
		for _, l := range r.Lines {
			b.WriteString(l + "\n")
		}
		first, prevLong = false, long
	}
	printed := map[string]bool{}
	for _, view := range e.views(m) {
		reasons := map[string]bool{}
		for _, p := range e.objects(m, "gives reasons for", view) {
			reasons[p] = true
		}
		patterns := e.objects(m, "shows", view)
		position := func(p string) int {
			if pos, ok := e.positions[Fact{Pred: "shows", Args: []Value{text(view), text(p)}}.key()]; ok {
				return pos
			}
			return len(e.rules)
		}
		sort.SliceStable(patterns, func(i, j int) bool { return position(patterns[i]) < position(patterns[j]) })
		b.WriteString("\n")
		for _, p := range patterns {
			pred, ok := e.patternPred[p]
			if !ok {
				continue
			}
			for _, f := range sortFacts(byPred[pred]) {
				if printed[f.key()] {
					continue
				}
				printed[f.key()] = true
				line := e.line(f)
				b.WriteString(line + "\n")
				if !reasons[p] {
					continue
				}
				for _, h := range e.reasonsFor[line] {
					if !printed[h.key()] {
						printed[h.key()] = true
						b.WriteString(e.line(h) + "\n")
					}
				}
			}
		}
	}
	return b.String()
}

func quoteIdent(s string) string {
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func (e *Engine) records(m *Model, answer string, all []Fact) (map[string][]map[string]any, error) {
	recs := map[string][]map[string]any{}
	for _, r := range e.rules {
		if r.Bad {
			continue
		}
		joined := strings.Join(r.Lines, "\n")
		recs["every rule"] = append(recs["every rule"], map[string]any{
			"the rule id":             sha16(joined),
			"the rule name":           r.Name,
			"the file the rule is in": r.File,
			"the number of the line the rule starts on": int64(r.Line),
			"the rule lines joined by newlines":         joined,
		})
	}
	creators := map[string][]string{}
	for _, f := range m.facts["creates"] {
		if len(f.Args) == 2 {
			creators[f.Args[1].plain()] = append(creators[f.Args[1].plain()], f.Args[0].plain())
		}
	}
	for _, f := range sortFacts(all) {
		line := e.line(f)
		files := creators[f.Pred]
		sort.Strings(files)
		recs["every fact"] = append(recs["every fact"], map[string]any{
			"the fact id":                sha16(line),
			"the fact as one plain line": line,
			"the file that creates the predicate of the fact": strings.Join(files, ", "),
		})
	}
	for _, d := range e.derivations {
		recs["every way a rule derives a fact"] = append(recs["every way a rule derives a fact"], map[string]any{
			"the derivation id": d.ID,
			"the fact id":       sha16(d.Line),
			"the rule name":     d.Rule.Name,
		})
		for i, reason := range d.Reasons {
			recs["every reason of every derivation"] = append(recs["every reason of every derivation"], map[string]any{
				"the derivation id":                                      d.ID,
				"the number of the condition in the rule":                int64(i + 1),
				"the condition with its blanks filled as one plain line": reason,
			})
		}
	}
	for _, part := range e.objects(m, "holds", "the certificate") {
		switch part {
		case hashPart:
			files := e.objects(m, "loads", engineFile)
			sort.SliceStable(files, func(i, j int) bool {
				return e.positions[Fact{Pred: "loads", Args: []Value{text(engineFile), text(files[i])}}.key()] <
					e.positions[Fact{Pred: "loads", Args: []Value{text(engineFile), text(files[j])}}.key()]
			})
			for _, file := range files {
				data, ok := e.contents[file]
				if !ok {
					return nil, fmt.Errorf("engine.go did not load %s, so it cannot hash it", file)
				}
				sum := sha256.Sum256(data)
				recs["every part the certificate holds"] = append(recs["every part the certificate holds"], map[string]any{
					"what the certificate holds":                     part,
					"the file a hash is of and empty for the answer": file,
					"the sha256 of the file in hex or the answer":    hex.EncodeToString(sum[:]),
				})
			}
		case answerPart:
			recs["every part the certificate holds"] = append(recs["every part the certificate holds"], map[string]any{
				"what the certificate holds":                     part,
				"the file a hash is of and empty for the answer": "",
				"the sha256 of the file in hex or the answer":    answer,
			})
		}
	}
	return recs, nil
}

func (e *Engine) publish(plan storePlan, recs map[string][]map[string]any) error {
	temp := plan.path + ".publishing"
	os.Remove(temp)
	defer os.Remove(temp)
	db, err := sql.Open("sqlite", temp)
	if err != nil {
		return err
	}
	defer db.Close()
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	defer tx.Rollback()
	for _, t := range plan.tables {
		cols := make([]string, len(t.columns))
		marks := make([]string, len(t.columns))
		for i, c := range t.columns {
			cols[i], marks[i] = quoteIdent(c.name), "?"
		}
		if _, err := tx.Exec("CREATE TABLE " + quoteIdent(t.name) + " (" + strings.Join(cols, ", ") + ")"); err != nil {
			return err
		}
		stmt, err := tx.Prepare("INSERT INTO " + quoteIdent(t.name) + " VALUES (" + strings.Join(marks, ", ") + ")")
		if err != nil {
			return err
		}
		for _, rec := range recs[t.kind] {
			vals := make([]any, len(t.columns))
			for i, c := range t.columns {
				vals[i] = rec[c.meaning]
			}
			if _, err := stmt.Exec(vals...); err != nil {
				stmt.Close()
				return err
			}
		}
		stmt.Close()
	}
	if err := tx.Commit(); err != nil {
		return err
	}
	if err := db.Close(); err != nil {
		return err
	}
	return os.Rename(temp, plan.path)
}

func (e *Engine) shouldPublish(plan storePlan, answer string) bool {
	if len(plan.onlyWhen) == 0 {
		return true
	}
	for _, a := range plan.onlyWhen {
		if a == answer {
			return true
		}
	}
	return false
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "engine.go needs the file it starts from")
		os.Exit(2)
	}
	os.Exit(run(os.Args[1]))
}

func run(entry string) int {
	e := newEngine(entry)
	e.load()
	e.prepare()
	m := e.solve()
	var plans []storePlan
	if m != nil {
		e.derive(m)
		e.explain(m)
		e.checkInstructions(m)
		plans = e.plans(m)
	}
	e.checkCreations()
	answer, code := e.decide(m)
	if m != nil {
		for _, plan := range plans {
			if !e.shouldPublish(plan, answer) {
				continue
			}
			recs, err := e.records(m, answer, e.knowledge(m))
			if err == nil {
				err = e.publish(plan, recs)
			}
			if err != nil {
				e.problem("the knowledge view cannot be published to %s: %v", plan.path, err)
				answer, code = e.decide(m)
			}
		}
	}
	out := e.render(m, e.knowledge(m))
	places := []string{"standard output"}
	if m != nil {
		places = e.objects(m, "prints to", engineFile)
	}
	for _, place := range places {
		switch place {
		case "standard output":
			os.Stdout.WriteString(out)
		case "standard error":
			os.Stderr.WriteString(out)
		}
	}
	return code
}
