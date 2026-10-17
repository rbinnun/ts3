package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	engineFile     = "engine.go"
	toolsFile      = "tools.go"
	firstFile      = "spec.plain"
	changeVariable = "THIS_RUN_IS_A_CHANGE"
	indent         = "    "
	maxRounds      = 50
	plainLanguage  = "plain language"
	mangleLanguage = "mangle"
)

var (
	wordShape   = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	varShape    = regexp.MustCompile(`^\[([a-z][a-z0-9]*(?: [a-z0-9]+)*)\]$`)
	numberShape = regexp.MustCompile(`^(0|-?[1-9][0-9]*)$`)
	patternVar  = regexp.MustCompile(`\[[a-z][a-z0-9]*(?: [a-z0-9]+)*\]`)
)

type termKind int

const (
	variableTerm termKind = iota
	stringTerm
	numberTerm
)

type term struct {
	kind   termKind
	text   string
	number int64
}

type litKind int

const (
	atomLit litKind = iota
	endsLit
	startsLit
	differsLit
	joinLit
)

var builtinWords = map[string]litKind{
	"ends with":      endsLit,
	"starts with":    startsLit,
	"differs from":   differsLit,
	"is the join of": joinLit,
}

type lit struct {
	kind    litKind
	negated bool
	word    string
	args    []term
}

type clause struct {
	file   string
	line   int
	gap    bool
	head   lit
	body   []lit
	source []string
	said   []string
	mangle string
}

func (c *clause) id() string {
	return fmt.Sprintf("%s:%d", c.file, c.line)
}

type field struct {
	text   string
	quoted bool
}

func splitFields(s string) ([]field, error) {
	var fields []field
	for {
		if s != "" && (s[0] == '"' || s[0] == '\'') {
			q := s[0]
			end := -1
			for i := 1; i < len(s); i++ {
				if s[i] == q && (i == len(s)-1 || strings.HasPrefix(s[i+1:], ", ")) {
					end = i
					break
				}
			}
			if end < 0 {
				return nil, fmt.Errorf("has a quote that never closes")
			}
			fields = append(fields, field{text: s[1:end], quoted: true})
			if end == len(s)-1 {
				return fields, nil
			}
			s = s[end+3:]
			continue
		}
		i := strings.Index(s, ", ")
		if i < 0 {
			return append(fields, field{text: s}), nil
		}
		fields = append(fields, field{text: s[:i]})
		s = s[i+2:]
	}
}

func readTerm(f field) term {
	if f.quoted {
		return term{kind: stringTerm, text: f.text}
	}
	if m := varShape.FindStringSubmatch(f.text); m != nil {
		return term{kind: variableTerm, text: m[1]}
	}
	if numberShape.MatchString(f.text) {
		if n, err := strconv.ParseInt(f.text, 10, 64); err == nil {
			return term{kind: numberTerm, number: n}
		}
	}
	return term{kind: stringTerm, text: f.text}
}

func readTerms(fields []field) []term {
	terms := make([]term, len(fields))
	for i, f := range fields {
		terms[i] = readTerm(f)
	}
	return terms
}

func readLit(s string, premise bool) (lit, error) {
	fields, err := splitFields(s)
	if err != nil {
		return lit{}, err
	}
	for _, f := range fields {
		if !f.quoted && f.text == "" {
			return lit{}, fmt.Errorf("has an empty part")
		}
	}
	switch len(fields) {
	case 1:
		if fields[0].quoted || !wordShape.MatchString(fields[0].text) {
			return lit{}, fmt.Errorf("is neither a word nor a fact")
		}
		return lit{kind: atomLit, word: fields[0].text}, nil
	case 2:
		return lit{}, fmt.Errorf("has two parts")
	}
	verb := fields[1]
	if verb.quoted || !wordShape.MatchString(verb.text) {
		return lit{}, fmt.Errorf("has no word in its second part")
	}
	if kind, ok := builtinWords[verb.text]; ok {
		if !premise {
			return lit{}, fmt.Errorf("says %s outside a premise", verb.text)
		}
		if kind != joinLit && len(fields) != 3 {
			return lit{}, fmt.Errorf("says %s with more than three parts", verb.text)
		}
		args := readTerms(append([]field{fields[0]}, fields[2:]...))
		return lit{kind: kind, word: verb.text, args: args}, nil
	}
	if verb.text == "is" && len(fields) == 3 && !fields[2].quoted && wordShape.MatchString(fields[2].text) {
		return lit{kind: atomLit, word: fields[2].text, args: []term{readTerm(fields[0])}}, nil
	}
	args := readTerms(append([]field{fields[0]}, fields[2:]...))
	return lit{kind: atomLit, word: verb.text, args: args}, nil
}

func readPremise(line string) (lit, error) {
	rest := strings.TrimLeft(line, " \t")
	var body string
	switch {
	case strings.HasPrefix(rest, "if "):
		body = rest[len("if "):]
	case strings.HasPrefix(rest, "and "):
		body = rest[len("and "):]
	default:
		return lit{}, fmt.Errorf("starts with neither if nor and")
	}
	negated := false
	if strings.HasPrefix(body, "not ") {
		negated = true
		body = body[len("not "):]
	}
	l, err := readLit(body, true)
	if err != nil {
		return lit{}, err
	}
	if negated && (l.kind == differsLit || l.kind == joinLit) {
		return lit{}, fmt.Errorf("cannot say not before %s", l.word)
	}
	l.negated = negated
	return l, nil
}

func readText(name, text string) ([]*clause, []string) {
	var clauses []*clause
	var problems []string
	var current *clause
	skipping, gap := false, false
	lines := strings.Split(text, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	for i, line := range lines {
		no := i + 1
		if strings.TrimSpace(line) == "" {
			current, skipping, gap = nil, false, true
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			if skipping {
				continue
			}
			if current == nil {
				problems = append(problems, fmt.Sprintf("%s line %d follows no fact: %s", name, no, strings.TrimSpace(line)))
				skipping = true
				continue
			}
			l, err := readPremise(line)
			if err != nil {
				problems = append(problems, fmt.Sprintf("%s line %d %s: %s", name, no, err, strings.TrimSpace(line)))
				clauses = clauses[:len(clauses)-1]
				current, skipping = nil, true
				continue
			}
			current.body = append(current.body, l)
			current.source = append(current.source, line)
			continue
		}
		skipping = false
		l, err := readLit(line, false)
		if err != nil {
			problems = append(problems, fmt.Sprintf("%s line %d %s: %s", name, no, err, line))
			current, skipping = nil, true
			continue
		}
		current = &clause{file: name, line: no, gap: gap, head: l, source: []string{line}}
		gap = false
		clauses = append(clauses, current)
	}
	return clauses, problems
}

func camel(words string) string {
	var b strings.Builder
	for _, w := range strings.Split(words, " ") {
		b.WriteString(strings.ToUpper(w[:1]))
		b.WriteString(w[1:])
	}
	return b.String()
}

func uncamel(name string) string {
	var b strings.Builder
	for i, r := range name {
		if unicode.IsUpper(r) {
			if i > 0 {
				b.WriteByte(' ')
			}
			b.WriteRune(unicode.ToLower(r))
			continue
		}
		b.WriteRune(r)
	}
	return b.String()
}

func predicateName(word string) string {
	return strings.ReplaceAll(word, " ", "_")
}

func wordOf(name string) string {
	return strings.ReplaceAll(name, "_", " ")
}

func (t term) mangle() string {
	switch t.kind {
	case variableTerm:
		return camel(t.text)
	case numberTerm:
		return strconv.FormatInt(t.number, 10)
	}
	return ast.String(t.text).String()
}

func (t term) plain() string {
	switch t.kind {
	case variableTerm:
		return "[" + t.text + "]"
	case numberTerm:
		return strconv.FormatInt(t.number, 10)
	}
	return t.text
}

func (t term) constant() (ast.Constant, bool) {
	switch t.kind {
	case stringTerm:
		return ast.String(t.text), true
	case numberTerm:
		return ast.Number(t.number), true
	}
	return ast.Constant{}, false
}

func mangleTerms(terms []term) string {
	parts := make([]string, len(terms))
	for i, t := range terms {
		parts[i] = t.mangle()
	}
	return strings.Join(parts, ", ")
}

func (l lit) mangle() string {
	not := ""
	if l.negated {
		not = "!"
	}
	switch l.kind {
	case endsLit:
		return not + ":string:ends_with(" + mangleTerms(l.args) + ")"
	case startsLit:
		return not + ":string:starts_with(" + mangleTerms(l.args) + ")"
	case differsLit:
		return l.args[0].mangle() + " != " + l.args[1].mangle()
	case joinLit:
		return l.args[0].mangle() + " = fn:string:concat(" + mangleTerms(l.args[1:]) + ")"
	}
	return not + predicateName(l.word) + "(" + mangleTerms(l.args) + ")"
}

func (l lit) symbol() ast.PredicateSym {
	return ast.PredicateSym{Symbol: predicateName(l.word), Arity: len(l.args)}
}

func (l lit) sentence() string {
	switch len(l.args) {
	case 0:
		return l.word
	case 1:
		return l.args[0].plain() + " is " + l.word
	}
	parts := []string{l.args[0].plain(), l.word}
	for _, t := range l.args[1:] {
		parts = append(parts, t.plain())
	}
	return strings.Join(parts, " ")
}

func (c *clause) toMangle() string {
	s := c.head.mangle()
	if len(c.body) > 0 {
		parts := make([]string, len(c.body))
		for i, l := range c.body {
			parts[i] = l.mangle()
		}
		s += " :- " + strings.Join(parts, ", ")
	}
	return s + "."
}

func lineToMangle(text string) (string, error) {
	l, err := readLit(text, true)
	if err != nil {
		return "", err
	}
	if l.kind == atomLit {
		return l.mangle() + ".", nil
	}
	return l.mangle(), nil
}

const (
	anyRole        = 0
	premiseSubject = 1 << iota
	isObject
)

func needsQuotes(s string, role int) bool {
	if s == "" || strings.TrimSpace(s) != s || strings.Contains(s, ", ") ||
		strings.HasPrefix(s, `"`) || strings.HasPrefix(s, "'") ||
		varShape.MatchString(s) || numberShape.MatchString(s) || strings.ContainsAny(s, "\n\r") {
		return true
	}
	if role&premiseSubject != 0 && strings.HasPrefix(s, "not ") {
		return true
	}
	return role&isObject != 0 && wordShape.MatchString(s)
}

func sayString(s string, role int) string {
	if !needsQuotes(s, role) {
		return s
	}
	for _, q := range []string{`"`, "'"} {
		if !strings.Contains(s, q+", ") && !strings.HasSuffix(s, q) {
			return q + s + q
		}
	}
	return `"` + s + `"`
}

func sayTerm(t ast.BaseTerm, role int) (string, error) {
	switch v := t.(type) {
	case ast.Variable:
		return "[" + uncamel(v.Symbol) + "]", nil
	case ast.Constant:
		switch v.Type {
		case ast.NumberType:
			return strconv.FormatInt(v.NumValue, 10), nil
		case ast.StringType:
			s, err := v.StringValue()
			if err != nil {
				return "", err
			}
			return sayString(s, role), nil
		}
	}
	return "", fmt.Errorf("%v has no plain words", t)
}

func sayParts(subject ast.BaseTerm, subjectRole int, word string, rest []ast.BaseTerm) (string, error) {
	s, err := sayTerm(subject, subjectRole)
	if err != nil {
		return "", err
	}
	parts := []string{s, word}
	for _, t := range rest {
		p, err := sayTerm(t, anyRole)
		if err != nil {
			return "", err
		}
		parts = append(parts, p)
	}
	return strings.Join(parts, ", "), nil
}

func sayAtom(a ast.Atom, subjectRole int) (string, error) {
	switch a.Predicate.Symbol {
	case ":string:ends_with":
		return sayParts(a.Args[0], subjectRole, "ends with", a.Args[1:])
	case ":string:starts_with":
		return sayParts(a.Args[0], subjectRole, "starts with", a.Args[1:])
	}
	if strings.Contains(a.Predicate.Symbol, ":") {
		return "", fmt.Errorf("%s has no plain words", a.Predicate.Symbol)
	}
	word := wordOf(a.Predicate.Symbol)
	switch len(a.Args) {
	case 0:
		return word, nil
	case 1:
		s, err := sayTerm(a.Args[0], subjectRole)
		if err != nil {
			return "", err
		}
		return s + ", is, " + word, nil
	}
	if word == "is" && len(a.Args) == 2 {
		s, err := sayTerm(a.Args[0], subjectRole)
		if err != nil {
			return "", err
		}
		o, err := sayTerm(a.Args[1], isObject)
		if err != nil {
			return "", err
		}
		return s + ", is, " + o, nil
	}
	return sayParts(a.Args[0], subjectRole, word, a.Args[1:])
}

func sayPremise(t ast.Term) (string, error) {
	switch p := t.(type) {
	case ast.Atom:
		return sayAtom(p, premiseSubject)
	case ast.NegAtom:
		s, err := sayAtom(p.Atom, anyRole)
		if err != nil {
			return "", err
		}
		return "not " + s, nil
	case ast.Ineq:
		return sayParts(p.Left, premiseSubject, "differs from", []ast.BaseTerm{p.Right})
	case ast.Eq:
		if fn, ok := p.Right.(ast.ApplyFn); ok && fn.Function.Symbol == "fn:string:concat" {
			return sayParts(p.Left, premiseSubject, "is the join of", fn.Args)
		}
	}
	return "", fmt.Errorf("%v has no plain words", t)
}

func sayClause(c ast.Clause) ([]string, error) {
	if c.Transform != nil || c.HeadTime != nil {
		return nil, fmt.Errorf("%v has no plain words", c)
	}
	head, err := sayAtom(c.Head, anyRole)
	if err != nil {
		return nil, err
	}
	lines := []string{head}
	for i, p := range c.Premises {
		s, err := sayPremise(p)
		if err != nil {
			return nil, err
		}
		lead := indent + "and "
		if i == 0 {
			lead = indent + "if "
		}
		lines = append(lines, lead+s)
	}
	return lines, nil
}

func readBack(mangle string) ([]string, error) {
	c, err := parse.Clause(mangle)
	if err != nil {
		return nil, err
	}
	return sayClause(c)
}

func oneLine(err error) string {
	return strings.Join(strings.Fields(err.Error()), " ")
}

type reading struct {
	clauses  []*clause
	problems []string
	misreads []string
}

func readFiles(files []string) reading {
	var r reading
	for _, name := range files {
		data, err := os.ReadFile(name)
		if err != nil {
			continue
		}
		clauses, problems := readText(name, string(data))
		r.problems = append(r.problems, problems...)
		for _, c := range clauses {
			c.mangle = c.toMangle()
			said, err := readBack(c.mangle)
			if err != nil {
				r.problems = append(r.problems, fmt.Sprintf("%s line %d cannot be said in mangle: %s", c.file, c.line, oneLine(err)))
				continue
			}
			c.said = said
			for i, line := range c.source {
				if i >= len(said) || said[i] != line {
					r.misreads = append(r.misreads, line)
				}
			}
			r.clauses = append(r.clauses, c)
		}
	}
	return r
}

type knowledge struct {
	store factstore.FactStore
	known map[ast.PredicateSym]bool
}

func emptyKnowledge() *knowledge {
	return &knowledge{store: factstore.NewSimpleInMemoryStore(), known: map[ast.PredicateSym]bool{}}
}

func knownPredicates(clauses []*clause) map[ast.PredicateSym]bool {
	known := map[ast.PredicateSym]bool{}
	for _, c := range clauses {
		known[c.head.symbol()] = true
		for _, l := range c.body {
			if l.kind == atomLit {
				known[l.symbol()] = true
			}
		}
	}
	return known
}

func constText(c ast.Constant) string {
	switch c.Type {
	case ast.StringType:
		s, _ := c.StringValue()
		return s
	case ast.NumberType:
		return strconv.FormatInt(c.NumValue, 10)
	}
	return c.String()
}

func (k *knowledge) atoms(sym ast.PredicateSym) []ast.Atom {
	var out []ast.Atom
	k.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
		out = append(out, a)
		return nil
	})
	return out
}

func (k *knowledge) facts(word string, arity int) [][]ast.Constant {
	var out [][]ast.Constant
	for _, a := range k.atoms(ast.PredicateSym{Symbol: predicateName(word), Arity: arity}) {
		row := make([]ast.Constant, 0, len(a.Args))
		for _, t := range a.Args {
			if c, ok := t.(ast.Constant); ok {
				row = append(row, c)
			}
		}
		if len(row) == arity {
			out = append(out, row)
		}
	}
	return out
}

func (k *knowledge) objects(word, subject string) []ast.Constant {
	var out []ast.Constant
	for _, row := range k.facts(word, 2) {
		if constText(row[0]) == subject {
			out = append(out, row[1])
		}
	}
	sort.Slice(out, func(i, j int) bool { return constText(out[i]) < constText(out[j]) })
	return out
}

func (k *knowledge) readPattern(s string) (string, int, bool) {
	word, arity, ok := readPattern(s)
	if ok && arity == 0 && !k.known[ast.PredicateSym{Symbol: predicateName(word), Arity: 0}] {
		return "", 0, false
	}
	return word, arity, ok
}

func readPattern(s string) (string, int, bool) {
	if strings.Contains(s, ", ") || strings.ContainsAny(s, "\"'\n") {
		return "", 0, false
	}
	locs := patternVar.FindAllStringIndex(s, -1)
	if len(locs) == 0 {
		return s, 0, wordShape.MatchString(s)
	}
	if locs[0][0] != 0 || locs[len(locs)-1][1] != len(s) && len(locs) > 1 {
		return "", 0, false
	}
	if len(locs) == 1 {
		rest := s[locs[0][1]:]
		if !strings.HasPrefix(rest, " is ") || !wordShape.MatchString(rest[len(" is "):]) {
			return "", 0, false
		}
		return rest[len(" is "):], 1, true
	}
	middle := s[locs[0][1]:locs[1][0]]
	if len(middle) < 3 || middle[0] != ' ' || middle[len(middle)-1] != ' ' {
		return "", 0, false
	}
	word := middle[1 : len(middle)-1]
	if !wordShape.MatchString(word) {
		return "", 0, false
	}
	for i := 2; i < len(locs); i++ {
		if s[locs[i-1][1]:locs[i][0]] != " " {
			return "", 0, false
		}
	}
	return word, len(locs), true
}

func (k *knowledge) does(file, instruction, word string, arity int) bool {
	for _, row := range k.facts(instruction, 2) {
		if constText(row[0]) != file || row[1].Type != ast.StringType {
			continue
		}
		if w, n, ok := k.readPattern(constText(row[1])); ok && w == word && n == arity {
			return true
		}
	}
	return false
}

func (k *knowledge) executes(file, word string, arity int) bool {
	return k.does(file, "executes instruction", word, arity)
}

func (k *knowledge) creates(file, word string, arity int) bool {
	return k.does(file, "creates fact", word, arity)
}

func stringConstants(clauses []*clause) []string {
	var out []string
	seen := map[string]bool{}
	visit := func(l lit) {
		for _, t := range l.args {
			if t.kind == stringTerm && !seen[t.text] {
				seen[t.text] = true
				out = append(out, t.text)
			}
		}
	}
	for _, c := range clauses {
		visit(c.head)
		for _, l := range c.body {
			visit(l)
		}
	}
	return out
}

type factList struct {
	atoms []ast.Atom
	seen  map[string]bool
}

func (f *factList) add(word string, args ...ast.BaseTerm) {
	a := ast.NewAtom(predicateName(word), args...)
	key := a.String()
	if f.seen == nil {
		f.seen = map[string]bool{}
	}
	if !f.seen[key] {
		f.seen[key] = true
		f.atoms = append(f.atoms, a)
	}
}

func engineFacts(prev *knowledge, clauses []*clause, problems, misreads []string, known map[ast.PredicateSym]bool) []ast.Atom {
	var f factList
	s := func(text string) ast.BaseTerm { return ast.String(text) }
	if prev.creates(engineFile, "this run is a change", 0) && os.Getenv(changeVariable) != "" {
		f.add("this run is a change")
	}
	if prev.creates(engineFile, "a problem", 1) {
		for _, p := range problems {
			f.add("a problem", s(p))
		}
	}
	if prev.creates(engineFile, "misread", 1) {
		for _, m := range misreads {
			f.add("misread", s(m))
		}
	}
	hasRule := prev.creates(engineFile, "has a rule for", 2)
	defines := prev.creates(engineFile, "defines", 2)
	refers := prev.creates(engineFile, "refers to", 2)
	laysDown := prev.creates(engineFile, "lays down", 2)
	for _, c := range clauses {
		if hasRule {
			f.add("has a rule for", s(c.file), s(c.head.word))
		}
		if defines {
			f.add("defines", s(c.id()), s(c.head.word))
		}
		if refers {
			for _, l := range c.body {
				if l.kind == atomLit {
					f.add("refers to", s(c.id()), s(l.word))
				}
			}
		}
		if laysDown && c.head.word == "breaks" && len(c.head.args) == 2 {
			if law, ok := c.head.args[1].constant(); ok {
				f.add("lays down", s(c.id()), law)
			}
		}
	}
	if prev.creates(engineFile, "names", 2) {
		k := &knowledge{store: prev.store, known: known}
		for _, text := range stringConstants(clauses) {
			if word, _, ok := k.readPattern(text); ok {
				f.add("names", s(text), s(word))
			}
		}
	}
	return f.atoms
}

type command struct {
	name, tool, input string
}

func toolFacts(prev *knowledge, results map[command][]outcome) []ast.Atom {
	if !prev.creates(toolsFile, "returned", 3) {
		return nil
	}
	var commands []command
	for c := range results {
		commands = append(commands, c)
	}
	sort.Slice(commands, func(i, j int) bool {
		a, b := commands[i], commands[j]
		if a.name != b.name {
			return a.name < b.name
		}
		if a.tool != b.tool {
			return a.tool < b.tool
		}
		return a.input < b.input
	})
	var f factList
	for _, c := range commands {
		for _, o := range results[c] {
			f.add("returned", ast.String(c.name), ast.String(o.field), o.value)
		}
	}
	return f.atoms
}

func (k *knowledge) meaningProblems() []string {
	if !k.executes(engineFile, "means in mangle", 2) {
		return nil
	}
	var problems []string
	for _, row := range k.facts("means in mangle", 2) {
		plain, mangle := constText(row[0]), constText(row[1])
		got, err := lineToMangle(plain)
		if err != nil {
			problems = append(problems, fmt.Sprintf("%s cannot be read: %s", plain, oneLine(err)))
			continue
		}
		if got != mangle {
			problems = append(problems, fmt.Sprintf("%s means in mangle %s and not %s", plain, got, mangle))
		}
	}
	sort.Strings(problems)
	return problems
}

func declText(p ast.PredicateSym) string {
	vars := make([]string, p.Arity)
	for i := range vars {
		vars[i] = fmt.Sprintf("X%d", i)
	}
	return fmt.Sprintf("Decl %s(%s).\n", p.Symbol, strings.Join(vars, ", "))
}

func programText(clauses []*clause, facts []ast.Atom) string {
	defined := map[ast.PredicateSym]bool{}
	referenced := map[ast.PredicateSym]bool{}
	var b strings.Builder
	for _, c := range clauses {
		defined[c.head.symbol()] = true
		for _, l := range c.body {
			if l.kind == atomLit {
				referenced[l.symbol()] = true
			}
		}
		b.WriteString(c.mangle)
		b.WriteByte('\n')
	}
	for _, a := range facts {
		defined[a.Predicate] = true
		b.WriteString(a.String())
		b.WriteString(".\n")
	}
	var decls []string
	for p := range referenced {
		if !defined[p] {
			decls = append(decls, declText(p))
		}
	}
	sort.Strings(decls)
	return strings.Join(decls, "") + b.String()
}

type analysed struct {
	info          *analysis.ProgramInfo
	strata        []analysis.Nodeset
	predToStratum map[ast.PredicateSym]int
}

func analyse(clauses []*clause, facts []ast.Atom) (analysed, error) {
	unit, err := parse.Unit(strings.NewReader(programText(clauses, facts)))
	if err != nil {
		return analysed{}, err
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		return analysed{}, err
	}
	strata, predToStratum, err := analysis.Stratify(analysis.Program{
		EdbPredicates: info.EdbPredicates,
		IdbPredicates: info.IdbPredicates,
		Rules:         info.Rules,
	})
	if err != nil {
		return analysed{}, err
	}
	return analysed{info, strata, predToStratum}, nil
}

func evaluate(clauses []*clause, facts []ast.Atom) (*knowledge, []*clause, []string) {
	var problems []string
	kept := clauses
	a, err := analyse(clauses, facts)
	if err != nil {
		kept = nil
		for _, c := range clauses {
			trial := append(append([]*clause{}, kept...), c)
			if _, err := analyse(trial, facts); err != nil {
				problems = append(problems, fmt.Sprintf("%s line %d cannot be used: %s", c.file, c.line, oneLine(err)))
				continue
			}
			kept = trial
		}
		a, err = analyse(kept, facts)
	}
	store := factstore.NewSimpleInMemoryStore()
	k := &knowledge{store: store, known: knownPredicates(kept)}
	if err != nil {
		return k, kept, append(problems, "the knowledge cannot be analysed: "+oneLine(err))
	}
	if _, err := engine.EvalStratifiedProgramWithStats(a.info, a.strata, a.predToStratum, store, engine.WithCreatedFactLimit(2000000)); err != nil {
		problems = append(problems, "the knowledge cannot be evaluated: "+oneLine(err))
	}
	return k, kept, problems
}

func signatureOf(files []string, facts []ast.Atom) string {
	parts := append([]string{}, files...)
	for _, a := range facts {
		parts = append(parts, a.String())
	}
	sort.Strings(parts)
	return strings.Join(parts, "\n")
}

func runCommands(k *knowledge, commands []command) map[command][]outcome {
	out := map[command][]outcome{}
	var mu sync.Mutex
	var wg sync.WaitGroup
	slots := make(chan struct{}, runtime.NumCPU())
	for _, c := range commands {
		wg.Add(1)
		go func(c command) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			r := useTool(k, c.tool, c.input)
			mu.Lock()
			out[c] = r
			mu.Unlock()
		}(c)
	}
	wg.Wait()
	return out
}

func fileExists(name string) bool {
	info, err := os.Stat(name)
	return err == nil && info.Mode().IsRegular()
}

type outcomeOfRun struct {
	k        *knowledge
	clauses  []*clause
	problems []string
	order    []string
}

func think() outcomeOfRun {
	files := []string{firstFile}
	loaded := map[string]bool{firstFile: true}
	results := map[command][]outcome{}
	prev := emptyKnowledge()
	signature := ""
	var carried []string
	carriedSeen := map[string]bool{}
	dropped := map[string]bool{}
	for round := 0; ; round++ {
		r := readFiles(files)
		var clauses []*clause
		for _, c := range r.clauses {
			if !dropped[c.id()] {
				clauses = append(clauses, c)
			}
		}
		problems := append(append(append([]string{}, r.problems...), prev.meaningProblems()...), carried...)
		known := knownPredicates(clauses)
		facts := engineFacts(prev, clauses, problems, r.misreads, known)
		facts = append(facts, toolFacts(prev, results)...)
		k, kept, evalProblems := evaluate(clauses, facts)
		var newFiles []string
		if k.executes(engineFile, "loads", 2) {
			for _, f := range k.objects("loads", engineFile) {
				name := constText(f)
				if !loaded[name] && filepath.IsLocal(name) && fileExists(name) {
					loaded[name] = true
					newFiles = append(newFiles, name)
				}
			}
		}
		var newCommands []command
		if k.executes(engineFile, "uses", 3) {
			for _, row := range k.facts("uses", 3) {
				c := command{constText(row[0]), constText(row[1]), constText(row[2])}
				if _, done := results[c]; !done {
					newCommands = append(newCommands, c)
				}
			}
		}
		sig := signatureOf(append(append([]string{}, files...), evalProblems...), facts)
		if (len(newFiles) == 0 && len(newCommands) == 0 && sig == signature) || round >= maxRounds {
			if round >= maxRounds {
				evalProblems = append(evalProblems, "the knowledge never settles")
			}
			return outcomeOfRun{k: k, clauses: kept, problems: append(problems, evalProblems...), order: stringConstants(kept)}
		}
		signature = sig
		files = append(files, newFiles...)
		for c, o := range runCommands(k, newCommands) {
			results[c] = o
		}
		for _, p := range evalProblems {
			if !carriedSeen[p] {
				carriedSeen[p] = true
				carried = append(carried, p)
			}
		}
		keptIDs := map[string]bool{}
		for _, c := range kept {
			keptIDs[c.id()] = true
		}
		for _, c := range clauses {
			if !keptIDs[c.id()] {
				dropped[c.id()] = true
			}
		}
		prev = k
	}
}

func shownOrder(k *knowledge, view string, clauses []*clause, order []string) func(string) int {
	rank := map[string]int{}
	for i, s := range order {
		rank[s] = i
	}
	stated := map[string]int{}
	for i, c := range clauses {
		if len(c.body) == 0 && c.head.word == "shows" && len(c.head.args) == 2 &&
			c.head.args[0].kind == stringTerm && c.head.args[0].text == view && c.head.args[1].kind == stringTerm {
			if _, ok := stated[c.head.args[1].text]; !ok {
				stated[c.head.args[1].text] = i
			}
		}
	}
	return func(p string) int {
		if i, ok := stated[p]; ok {
			return len(order) + i
		}
		if i, ok := rank[p]; ok {
			return i
		}
		return len(order) + len(clauses)
	}
}

func renderView(k *knowledge, view, language string, clauses []*clause, order []string) string {
	if language != plainLanguage && language != mangleLanguage {
		return ""
	}
	var b strings.Builder
	inView := "in " + view
	if wordShape.MatchString(inView) && k.executes(engineFile, inView, 1) {
		members := map[string]bool{}
		for _, row := range k.facts(inView, 1) {
			members[constText(row[0])] = true
		}
		var last *clause
		for _, c := range clauses {
			if !members[c.id()] {
				continue
			}
			if last != nil && (c.gap || c.file != last.file) {
				b.WriteString("\n")
			}
			if language == plainLanguage {
				for _, line := range c.said {
					b.WriteString(line + "\n")
				}
			} else {
				b.WriteString(c.mangle + "\n")
			}
			last = c
		}
	}
	if !k.executes(engineFile, "shows", 2) {
		return b.String()
	}
	var patterns []string
	for _, p := range k.objects("shows", view) {
		if p.Type == ast.StringType {
			patterns = append(patterns, constText(p))
		}
	}
	rank := shownOrder(k, view, clauses, order)
	sort.SliceStable(patterns, func(i, j int) bool { return rank(patterns[i]) < rank(patterns[j]) })
	seen := map[ast.PredicateSym]bool{}
	for _, p := range patterns {
		word, arity, ok := k.readPattern(p)
		if !ok {
			continue
		}
		sym := ast.PredicateSym{Symbol: predicateName(word), Arity: arity}
		if seen[sym] {
			continue
		}
		seen[sym] = true
		var lines []string
		for _, a := range k.atoms(sym) {
			if language == mangleLanguage {
				lines = append(lines, a.String()+".")
				continue
			}
			if s, err := sayAtom(a, anyRole); err == nil {
				lines = append(lines, s)
			}
		}
		if len(lines) == 0 {
			continue
		}
		sort.Strings(lines)
		sort.SliceStable(lines, func(i, j int) bool { return naturalLess(lines[i], lines[j]) })
		if b.Len() > 0 {
			b.WriteString("\n")
		}
		b.WriteString(strings.Join(lines, "\n") + "\n")
	}
	return b.String()
}

func digitRun(s string) int {
	n := 0
	for n < len(s) && s[n] >= '0' && s[n] <= '9' {
		n++
	}
	return n
}

func naturalLess(a, b string) bool {
	for a != "" && b != "" {
		da, db := digitRun(a), digitRun(b)
		if da > 0 && db > 0 {
			na, nb := strings.TrimLeft(a[:da], "0"), strings.TrimLeft(b[:db], "0")
			if len(na) != len(nb) {
				return len(na) < len(nb)
			}
			if na != nb {
				return na < nb
			}
			a, b = a[da:], b[db:]
			continue
		}
		if a[0] != b[0] {
			return a[0] < b[0]
		}
		a, b = a[1:], b[1:]
	}
	return len(a) < len(b)
}

func speak(o outcomeOfRun) {
	k := o.k
	if !k.executes(engineFile, "prints", 2) {
		return
	}
	var languages, places []ast.Constant
	if k.executes(engineFile, "prints in", 2) {
		languages = k.objects("prints in", engineFile)
	}
	if k.executes(engineFile, "prints to", 2) {
		places = k.objects("prints to", engineFile)
	}
	for _, view := range k.objects("prints", engineFile) {
		for _, language := range languages {
			text := renderView(k, constText(view), constText(language), o.clauses, o.order)
			for _, place := range places {
				switch constText(place) {
				case "standard output":
					os.Stdout.WriteString(text)
				case "standard error":
					os.Stderr.WriteString(text)
				}
			}
		}
	}
}

func answer(o outcomeOfRun) int {
	k := o.k
	verdict := "broken"
	if len(o.problems) == 0 || !k.executes(engineFile, "a problem", 1) {
		if k.executes(engineFile, "conforms", 2) {
			answers := map[string]bool{}
			for _, row := range k.facts("conforms", 2) {
				answers[constText(row[1])] = true
			}
			if len(answers) == 1 {
				for a := range answers {
					verdict = a
				}
			}
		}
	}
	if k.executes(engineFile, "exits with", 2) {
		for _, row := range k.facts("exits with", 2) {
			if constText(row[0]) == verdict && row[1].Type == ast.NumberType {
				return int(row[1].NumValue)
			}
		}
	}
	return 2
}

func main() {
	o := think()
	speak(o)
	os.Exit(answer(o))
}
