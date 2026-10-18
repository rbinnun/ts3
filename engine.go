package main

import (
	"bufio"
	"fmt"
	"os"
	"regexp"
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
	"codeberg.org/TauCeti/mangle-go/unionfind"
)

const (
	machine       = "engine.go"
	firstFile     = "spec.plain"
	theFolder     = "the folder"
	brokenAnswer  = "broken"
	knowledgeView = "the knowledge view"
	patternSlot   = "fact pattern"
	placeholder   = "PlainArg"
	maxRounds     = 50
)

var (
	wordsPattern  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	blankPattern  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z][a-z0-9]*)*$`)
	numberPattern = regexp.MustCompile(`^-?[0-9]+$`)
	slotPattern   = regexp.MustCompile(`\[[^\[\]]*\]`)
)

type kind int

const (
	textValue kind = iota
	numberValue
	blankValue
)

type value struct {
	kind kind
	text string
	num  int64
}

type atom struct {
	verb    string
	pred    string
	args    []value
	negated bool
	tpl     *template
}

type template struct {
	verb  string
	arity int
	text  string
	term  ast.Term
}

type raw struct {
	line    int
	lines   []string
	problem string
}

type part struct {
	text   string
	quoted bool
}

type statement struct {
	file       string
	line       int
	lines      []string
	id         string
	head       atom
	conds      []atom
	ok         bool
	problem    string
	translated bool
	usable     bool
	differs    bool
	clause     ast.Clause
	readBack   string
}

type event struct {
	clause ast.Clause
	subst  ast.ConstSubstList
}

type recorder struct {
	mu     sync.Mutex
	events map[string][]event
}

func (r *recorder) RuleFired(rule ast.Clause, head ast.Atom, subst unionfind.UnionFind, _ []ast.Atom) {
	r.mu.Lock()
	defer r.mu.Unlock()
	k := head.String()
	r.events[k] = append(r.events[k], event{rule, subst.AsConstSubstList()})
}

func (r *recorder) LetEmit(ast.Clause, ast.Atom, ast.ConstSubstList, ast.Atom) {}

func (r *recorder) DoEmit(ast.Clause, ast.Atom, []ast.Constant, []ast.Atom, ast.Atom) {}

type outcome struct {
	store    factstore.SimpleInMemoryStore
	events   map[string][]event
	problems int
	err      error
}

type position struct {
	pred  string
	arity int
	index int
}

type knower struct {
	statements    []*statement
	templates     map[string]*template
	templateOrder []string
	facts         []ast.Atom
	factSeen      map[string]bool
	problems      []string
	problemSeen   map[string]bool
	order         map[string]int
	written       map[string]string
	patterns      map[string]atom
	patternOrder  []string
	mu            sync.Mutex
}

func main() {
	k := &knower{
		templates:   map[string]*template{},
		factSeen:    map[string]bool{},
		problemSeen: map[string]bool{},
		order:       map[string]int{},
		written:     map[string]string{},
		patterns:    map[string]atom{},
	}
	k.load()
	k.learnTemplates()
	k.translate()
	k.describe()
	if os.Getenv(changeVariable) != "" {
		k.addFact(ast.NewAtom("this_run_is_a_change"))
	}
	os.Exit(k.finish(k.run()))
}

func (k *knower) addProblem(text string) {
	k.mu.Lock()
	defer k.mu.Unlock()
	if k.problemSeen[text] {
		return
	}
	k.problemSeen[text] = true
	k.problems = append(k.problems, text)
}

func (k *knower) problemAt(s *statement, text string) {
	k.addProblem(fmt.Sprintf("%s line %d: %s", s.file, s.line, text))
}

func (k *knower) addFact(a ast.Atom) {
	key := a.String()
	if k.factSeen[key] {
		return
	}
	k.factSeen[key] = true
	k.facts = append(k.facts, a)
}

func (k *knower) fact(pred string, args ...string) {
	terms := make([]ast.BaseTerm, len(args))
	for i, a := range args {
		terms[i] = ast.String(a)
	}
	k.addFact(ast.NewAtom(mangleName(pred), terms...))
}

func (k *knower) load() {
	queue := []string{firstFile}
	loaded := map[string]bool{}
	for len(queue) > 0 {
		file := queue[0]
		queue = queue[1:]
		if loaded[file] {
			continue
		}
		loaded[file] = true
		src, err := os.ReadFile(file)
		if err != nil {
			if file == firstFile {
				k.addProblem(fmt.Sprintf("engine.go can't read %s", file))
			}
			continue
		}
		raws, loose := splitStatements(string(src))
		for _, l := range loose {
			k.addProblem(file + " " + l)
		}
		for _, r := range raws {
			s := parseStatement(file, r)
			k.statements = append(k.statements, s)
			if !s.ok {
				k.problemAt(s, s.problem)
				continue
			}
			if f, ok := s.loads(); ok {
				queue = append(queue, f)
			}
		}
	}
}

func (s *statement) loads() (string, bool) {
	h := s.head
	if len(s.conds) > 0 || h.verb != "loads" || len(h.args) != 2 {
		return "", false
	}
	if h.args[0].kind != textValue || h.args[0].text != machine || h.args[1].kind != textValue {
		return "", false
	}
	return h.args[1].text, true
}

func splitStatements(src string) ([]raw, []string) {
	var out []raw
	var loose []string
	open := false
	lines := strings.Split(src, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	for i, l := range lines {
		t := strings.TrimLeft(l, " \t")
		switch {
		case strings.TrimSpace(l) == "":
			open = false
		case t != l:
			if !open {
				loose = append(loose, fmt.Sprintf("line %d: %s belongs to no rule", i+1, plainText(l)))
				continue
			}
			r := &out[len(out)-1]
			r.lines = append(r.lines, l)
			if r.problem == "" && !strings.HasPrefix(t, "if ") && !strings.HasPrefix(t, "and ") {
				r.problem = fmt.Sprintf("%s is indented, so it must start with if or and", plainText(l))
			}
		default:
			out = append(out, raw{line: i + 1, lines: []string{l}})
			open = true
		}
	}
	return out, loose
}

func parseStatement(file string, r raw) *statement {
	s := &statement{file: file, line: r.line, lines: r.lines}
	ids := []string{r.lines[0]}
	for _, l := range r.lines[1:] {
		ids = append(ids, strings.TrimLeft(l, " \t"))
	}
	s.id = strings.Join(ids, " ")
	if r.problem != "" {
		s.problem = r.problem
		return s
	}
	h, err := parseAtom(r.lines[0])
	if err != nil {
		s.problem = err.Error()
		return s
	}
	s.head = h
	for _, l := range r.lines[1:] {
		t := strings.TrimLeft(l, " \t")
		if strings.HasPrefix(t, "if ") {
			t = t[3:]
		} else {
			t = t[4:]
		}
		negated := strings.HasPrefix(t, "not ")
		if negated {
			t = t[4:]
		}
		c, err := parseAtom(t)
		if err != nil {
			s.problem = err.Error()
			return s
		}
		c.negated = negated
		s.conds = append(s.conds, c)
	}
	s.ok = true
	return s
}

func splitParts(s string) ([]part, error) {
	var parts []part
	i := 0
	for {
		if i < len(s) && (s[i] == '"' || s[i] == '\'') {
			q := s[i]
			var b strings.Builder
			j := i + 1
			closed := false
			for j < len(s) {
				c := s[j]
				if c == '\\' && j+1 < len(s) {
					switch s[j+1] {
					case 'n':
						b.WriteByte('\n')
					case 't':
						b.WriteByte('\t')
					case 'r':
						b.WriteByte('\r')
					default:
						b.WriteByte(s[j+1])
					}
					j += 2
					continue
				}
				j++
				if c == q {
					closed = true
					break
				}
				b.WriteByte(c)
			}
			if !closed {
				return nil, fmt.Errorf("%s has a quote that is never closed", s)
			}
			parts = append(parts, part{b.String(), true})
			if j == len(s) {
				return parts, nil
			}
			if !strings.HasPrefix(s[j:], ", ") {
				return nil, fmt.Errorf("%s has more after a closing quote than a comma", s)
			}
			i = j + 2
			continue
		}
		n := strings.Index(s[i:], ", ")
		if n < 0 {
			return append(parts, part{s[i:], false}), nil
		}
		parts = append(parts, part{s[i : i+n], false})
		i += n + 2
	}
}

func parseValue(p part) (value, error) {
	if p.quoted {
		return value{kind: textValue, text: p.text}, nil
	}
	t := p.text
	if blankShaped(t) {
		w := t[1 : len(t)-1]
		if !blankPattern.MatchString(w) {
			return value{}, fmt.Errorf("%s is not a blank, which is lowercase words in brackets", t)
		}
		return value{kind: blankValue, text: w}, nil
	}
	if numberPattern.MatchString(t) {
		n, err := strconv.ParseInt(t, 10, 64)
		if err != nil {
			return value{}, fmt.Errorf("%s is too big a number", t)
		}
		return value{kind: numberValue, num: n}, nil
	}
	return value{kind: textValue, text: t}, nil
}

func blankShaped(t string) bool {
	return strings.HasPrefix(t, "[") && strings.HasSuffix(t, "]") && strings.Count(t, "[") == 1 && strings.Count(t, "]") == 1
}

func parseAtom(s string) (atom, error) {
	parts, err := splitParts(s)
	if err != nil {
		return atom{}, err
	}
	switch len(parts) {
	case 1:
		if parts[0].quoted || !wordsPattern.MatchString(parts[0].text) {
			return atom{}, fmt.Errorf("%s is one part, so it must be a sentence of lowercase words", s)
		}
		return atom{pred: parts[0].text}, nil
	case 2:
		return atom{}, fmt.Errorf("%s has two parts, and a line has one part, or three or more", s)
	}
	verb := parts[1]
	if verb.quoted || !wordsPattern.MatchString(verb.text) {
		return atom{}, fmt.Errorf("in %s the verb %s is not lowercase words", s, verb.text)
	}
	var args []value
	for _, p := range append([]part{parts[0]}, parts[2:]...) {
		v, err := parseValue(p)
		if err != nil {
			return atom{}, err
		}
		args = append(args, v)
	}
	if verb.text == "is" {
		o := parts[2]
		if len(parts) != 3 || o.quoted || !wordsPattern.MatchString(o.text) {
			return atom{}, fmt.Errorf("in %s, is must be followed by one name of lowercase words", s)
		}
		return atom{verb: "is", pred: o.text, args: args[:1]}, nil
	}
	return atom{verb: verb.text, pred: verb.text, args: args}, nil
}

func parsePattern(t string) (atom, error) {
	locs := slotPattern.FindAllStringIndex(t, -1)
	if len(locs) == 0 {
		return parseAtom(t)
	}
	fail := fmt.Errorf("%s is not a fact pattern, which starts with a slot and puts its verb after it", t)
	if locs[0][0] != 0 {
		return atom{}, fail
	}
	parts := []string{t[:locs[0][1]]}
	if len(locs) == 1 {
		rest := t[locs[0][1]:]
		if !strings.HasPrefix(rest, " is ") {
			return atom{}, fail
		}
		parts = append(parts, "is", rest[4:])
	} else {
		verb := t[locs[0][1]:locs[1][0]]
		if len(verb) < 3 || verb[0] != ' ' || verb[len(verb)-1] != ' ' {
			return atom{}, fail
		}
		parts = append(parts, verb[1:len(verb)-1])
		for i := 1; i < len(locs); i++ {
			if i > 1 && t[locs[i-1][1]:locs[i][0]] != " " {
				return atom{}, fail
			}
			parts = append(parts, t[locs[i][0]:locs[i][1]])
		}
		if locs[len(locs)-1][1] != len(t) {
			return atom{}, fail
		}
	}
	return parseAtom(strings.Join(parts, ", "))
}

func mangleName(pred string) string {
	return strings.ReplaceAll(pred, " ", "_")
}

func camel(words string) string {
	var b strings.Builder
	for _, w := range strings.Fields(words) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	return b.String()
}

func uncamel(name string) string {
	var words []string
	start := 0
	for i, r := range name {
		if i > 0 && unicode.IsUpper(r) {
			words = append(words, strings.ToLower(name[start:i]))
			start = i
		}
	}
	words = append(words, strings.ToLower(name[start:]))
	return strings.Join(words, " ")
}

func mangleValue(v value) string {
	switch v.kind {
	case blankValue:
		return camel(v.text)
	case numberValue:
		return ast.Number(v.num).String()
	}
	return ast.String(v.text).String()
}

func (a atom) mangle() string {
	var s string
	if a.tpl != nil {
		s = a.tpl.fill(a.args)
	} else {
		args := make([]string, len(a.args))
		for i, v := range a.args {
			args[i] = mangleValue(v)
		}
		s = mangleName(a.pred) + "(" + strings.Join(args, ", ") + ")"
	}
	if a.negated {
		s = "!" + s
	}
	return s
}

func (s *statement) mangle() string {
	text := s.head.mangle()
	if len(s.conds) > 0 {
		conds := make([]string, len(s.conds))
		for i, c := range s.conds {
			conds[i] = c.mangle()
		}
		text += " :- " + strings.Join(conds, ", ")
	}
	return text + "."
}

func templateKey(verb string, arity int) string {
	return verb + "/" + strconv.Itoa(arity)
}

func (t *template) fill(args []value) string {
	toks := mangleTokens(t.text)
	for i, tok := range toks {
		if n, ok := placeholderNumber(tok); ok && n <= len(args) {
			toks[i] = mangleValue(args[n-1])
		}
	}
	return strings.Join(toks, "")
}

func placeholderNumber(s string) (int, bool) {
	if !strings.HasPrefix(s, placeholder) {
		return 0, false
	}
	n, err := strconv.Atoi(s[len(placeholder):])
	return n, err == nil && n > 0
}

func mangleTokens(s string) []string {
	var toks []string
	for i := 0; i < len(s); {
		j := i + 1
		switch c := s[i]; {
		case c == '"':
			for j < len(s) && s[j] != '"' {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			j++
			if j > len(s) {
				j = len(s)
			}
		case isWordByte(c):
			for j < len(s) && isWordByte(s[j]) {
				j++
			}
		}
		toks = append(toks, s[i:j])
		i = j
	}
	return toks
}

func isWordByte(c byte) bool {
	return c == '_' || c == ':' || c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

func (k *knower) learnTemplates() {
	for _, s := range k.statements {
		if !s.ok || len(s.conds) > 0 || s.head.verb != "means in mangle" || len(s.head.args) != 2 {
			continue
		}
		l, m := s.head.args[0], s.head.args[1]
		if l.kind != textValue || m.kind != textValue {
			continue
		}
		k.learn(s, l.text, m.text)
	}
}

func (k *knower) learn(s *statement, line, m string) {
	a, err := parseAtom(line)
	if err != nil {
		k.problemAt(s, fmt.Sprintf("%s can't mean anything in mangle: %v", line, err))
		return
	}
	plain := a.mangle() + "."
	if plain == m {
		return
	}
	if strings.HasSuffix(m, ".") || a.verb == "" || a.verb == "is" {
		k.problemAt(s, fmt.Sprintf("%s means %s in mangle, but engine.go writes it as %s", line, m, plain))
		return
	}
	renders := make([]string, len(a.args))
	for i, v := range a.args {
		renders[i] = mangleValue(v)
		for j := 0; j < i; j++ {
			if renders[j] == renders[i] {
				k.problemAt(s, fmt.Sprintf("%s uses %s twice, so engine.go can't learn from it", line, renders[i]))
				return
			}
		}
	}
	toks := mangleTokens(m)
	used := make([]bool, len(renders))
	for i, tok := range toks {
		for j, r := range renders {
			if tok == r {
				toks[i] = placeholder + strconv.Itoa(j+1)
				used[j] = true
				break
			}
		}
	}
	for j, u := range used {
		if !u {
			k.problemAt(s, fmt.Sprintf("%s means %s in mangle, which leaves out %s", line, m, renders[j]))
			return
		}
	}
	text := strings.Join(toks, "")
	term, err := parse.LiteralOrFormula(text)
	if err != nil {
		k.problemAt(s, fmt.Sprintf("%s means %s in mangle, which mangle can't read as a condition", line, m))
		return
	}
	key := templateKey(a.verb, len(a.args))
	if old, ok := k.templates[key]; ok {
		if old.text != text {
			k.problemAt(s, fmt.Sprintf("%s means %s in mangle, but %s already means something else", line, m, a.verb))
		}
		return
	}
	k.templates[key] = &template{verb: a.verb, arity: len(a.args), text: text, term: term}
	k.templateOrder = append(k.templateOrder, key)
}

func (k *knower) templateFor(a atom) *template {
	if a.verb == "" || a.verb == "is" {
		return nil
	}
	return k.templates[templateKey(a.verb, len(a.args))]
}

func (k *knower) resolve(s *statement) bool {
	if k.templateFor(s.head) != nil {
		k.problemAt(s, fmt.Sprintf("%s is only ever a condition", s.head.verb))
		return false
	}
	for i := range s.conds {
		c := &s.conds[i]
		t := k.templateFor(*c)
		if t == nil {
			continue
		}
		if c.negated {
			k.problemAt(s, fmt.Sprintf("engine.go can't put not before %s", c.verb))
			return false
		}
		c.tpl = t
	}
	return true
}

func (k *knower) translate() {
	for i, s := range k.statements {
		if !s.ok || !k.resolve(s) {
			continue
		}
		text := s.mangle()
		c, err := parse.Clause(text)
		if err != nil {
			k.problemAt(s, fmt.Sprintf("engine.go writes it in mangle as %s, which mangle can't read", text))
			continue
		}
		s.clause = c
		s.translated = true
		back, err := k.plainClause(c)
		if err == nil {
			s.readBack = back
		}
		s.differs = err != nil || back != strings.Join(s.lines, "\n")
		if err := checkAlone(c); err != nil {
			k.problemAt(s, fmt.Sprintf("mangle can't use it: %v", err))
		} else {
			s.usable = true
		}
		if len(s.conds) == 0 {
			key := c.Head.String()
			if _, ok := k.order[key]; !ok {
				k.order[key] = i
				k.written[key] = s.file
			}
		}
	}
}

func premiseAtom(p ast.Term) (ast.Atom, bool) {
	switch v := p.(type) {
	case ast.Atom:
		return v, !strings.HasPrefix(v.Predicate.Symbol, ":")
	case ast.NegAtom:
		return v.Atom, !strings.HasPrefix(v.Atom.Predicate.Symbol, ":")
	}
	return ast.Atom{}, false
}

func checkAlone(c ast.Clause) error {
	extras := map[ast.PredicateSym]ast.Decl{}
	for _, p := range c.Premises {
		if a, ok := premiseAtom(p); ok && a.Predicate != c.Head.Predicate {
			extras[a.Predicate] = ast.NewSyntheticDeclFromSym(a.Predicate)
		}
	}
	_, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: []ast.Clause{c}}, extras)
	return err
}

func needsQuotes(s string) bool {
	switch {
	case s == "", strings.TrimSpace(s) != s, strings.Contains(s, ", "):
		return true
	case strings.HasPrefix(s, "\""), strings.HasPrefix(s, "'"), strings.HasPrefix(s, "not "):
		return true
	case strings.ContainsAny(s, "\n\r\t"), numberPattern.MatchString(s), blankShaped(s):
		return true
	}
	return false
}

func quote(s string) string {
	q := byte('"')
	if strings.Contains(s, "\"") && !strings.Contains(s, "'") {
		q = '\''
	}
	var b strings.Builder
	b.WriteByte(q)
	for i := 0; i < len(s); i++ {
		switch c := s[i]; c {
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		case q:
			b.WriteByte('\\')
			b.WriteByte(c)
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte(q)
	return b.String()
}

func plainText(s string) string {
	if needsQuotes(s) {
		return quote(s)
	}
	return s
}

func plainTerm(t ast.BaseTerm) (string, error) {
	switch v := t.(type) {
	case ast.Variable:
		return "[" + uncamel(v.Symbol) + "]", nil
	case ast.Constant:
		switch v.Type {
		case ast.StringType:
			return plainText(v.Symbol), nil
		case ast.NumberType:
			return ast.FormatNumber(v.NumValue), nil
		}
	}
	return "", fmt.Errorf("%v has no plain form", t)
}

func constText(t ast.BaseTerm) string {
	if c, ok := t.(ast.Constant); ok {
		switch c.Type {
		case ast.StringType:
			return c.Symbol
		case ast.NumberType:
			return ast.FormatNumber(c.NumValue)
		}
	}
	return t.String()
}

func plainLine(words string, args []string) string {
	switch len(args) {
	case 0:
		return words
	case 1:
		return args[0] + ", is, " + words
	}
	return args[0] + ", " + words + ", " + strings.Join(args[1:], ", ")
}

func (k *knower) plainAtom(a ast.Atom) (string, error) {
	if strings.HasPrefix(a.Predicate.Symbol, ":") {
		return k.plainBuiltin(a)
	}
	args := make([]string, len(a.Args))
	for i, t := range a.Args {
		s, err := plainTerm(t)
		if err != nil {
			return "", err
		}
		args[i] = s
	}
	return plainLine(strings.ReplaceAll(a.Predicate.Symbol, "_", " "), args), nil
}

func (k *knower) plainPremise(p ast.Term) (string, error) {
	switch v := p.(type) {
	case ast.Atom:
		return k.plainAtom(v)
	case ast.NegAtom:
		s, err := k.plainAtom(v.Atom)
		return "not " + s, err
	}
	return k.plainBuiltin(p)
}

func (k *knower) plainBuiltin(p ast.Term) (string, error) {
	for _, key := range k.templateOrder {
		t := k.templates[key]
		binds := map[int]ast.BaseTerm{}
		if !matchTerm(t.term, p, binds) || len(binds) != t.arity {
			continue
		}
		args := make([]string, t.arity)
		for i := range args {
			s, err := plainTerm(binds[i+1])
			if err != nil {
				return "", err
			}
			args[i] = s
		}
		return args[0] + ", " + t.verb + ", " + strings.Join(args[1:], ", "), nil
	}
	return "", fmt.Errorf("%v has no plain form", p)
}

func matchTerm(t, a ast.Term, binds map[int]ast.BaseTerm) bool {
	switch tt := t.(type) {
	case ast.Atom:
		aa, ok := a.(ast.Atom)
		return ok && aa.Predicate == tt.Predicate && matchArgs(tt.Args, aa.Args, binds)
	case ast.Eq:
		aa, ok := a.(ast.Eq)
		return ok && matchBase(tt.Left, aa.Left, binds) && matchBase(tt.Right, aa.Right, binds)
	case ast.Ineq:
		aa, ok := a.(ast.Ineq)
		return ok && matchBase(tt.Left, aa.Left, binds) && matchBase(tt.Right, aa.Right, binds)
	}
	return false
}

func matchArgs(ts, as []ast.BaseTerm, binds map[int]ast.BaseTerm) bool {
	if len(ts) != len(as) {
		return false
	}
	for i := range ts {
		if !matchBase(ts[i], as[i], binds) {
			return false
		}
	}
	return true
}

func matchBase(t, a ast.BaseTerm, binds map[int]ast.BaseTerm) bool {
	switch tt := t.(type) {
	case ast.Variable:
		if n, ok := placeholderNumber(tt.Symbol); ok {
			if old, ok := binds[n]; ok {
				return old.Equals(a)
			}
			binds[n] = a
			return true
		}
	case ast.ApplyFn:
		aa, ok := a.(ast.ApplyFn)
		return ok && aa.Function.Symbol == tt.Function.Symbol && matchArgs(tt.Args, aa.Args, binds)
	}
	return t.Equals(a)
}

func (k *knower) plainClause(c ast.Clause) (string, error) {
	head, err := k.plainAtom(c.Head)
	if err != nil {
		return "", err
	}
	lines := []string{head}
	for i, p := range c.Premises {
		s, err := k.plainPremise(p)
		if err != nil {
			return "", err
		}
		lead := "    and "
		if i == 0 {
			lead = "    if "
		}
		lines = append(lines, lead+s)
	}
	return strings.Join(lines, "\n"), nil
}

func slotBase(w string) string {
	for _, p := range []string{"any ", "other "} {
		if strings.HasPrefix(w, p) {
			return w[len(p):]
		}
	}
	return w
}

func (k *knower) describe() {
	var atoms []atom
	var where []*statement
	for _, s := range k.statements {
		if !s.translated {
			continue
		}
		k.fact("has a rule for", s.file, s.head.pred)
		k.fact("defines", s.id, s.head.pred)
		for _, c := range s.conds {
			if c.tpl == nil {
				k.fact("refers to", s.id, c.pred)
			}
		}
		if h := s.head; h.verb == "breaks" && len(h.args) >= 2 {
			if law := h.args[len(h.args)-1]; law.kind == textValue {
				k.fact("lays down", s.id, law.text)
			}
		}
		for _, a := range append([]atom{s.head}, s.conds...) {
			for _, v := range a.args {
				if v.kind == blankValue {
					k.fact("has the blank", s.id, v.text)
				}
			}
			if a.tpl == nil {
				atoms = append(atoms, a)
				where = append(where, s)
			}
		}
		if s.differs {
			k.fact("read back differently", s.id)
		}
	}
	k.findPatterns(atoms, where)
}

func (k *knower) findPatterns(atoms []atom, where []*statement) {
	positions := map[position]bool{}
	mark := func(a atom) bool {
		grew := false
		for i, v := range a.args {
			if v.kind == blankValue && slotBase(v.text) == patternSlot {
				p := position{a.pred, len(a.args), i}
				if !positions[p] {
					positions[p] = true
					grew = true
				}
			}
		}
		return grew
	}
	for _, a := range atoms {
		mark(a)
	}
	bad := map[string]bool{}
	for grew := true; grew; {
		grew = false
		for n, a := range atoms {
			for i, v := range a.args {
				if v.kind != textValue || !positions[position{a.pred, len(a.args), i}] {
					continue
				}
				if _, ok := k.patterns[v.text]; ok || bad[v.text] {
					continue
				}
				p, err := parsePattern(v.text)
				if err != nil {
					bad[v.text] = true
					k.problemAt(where[n], err.Error())
					continue
				}
				k.patterns[v.text] = p
				k.patternOrder = append(k.patternOrder, v.text)
				if mark(p) {
					grew = true
				}
			}
		}
	}
	for _, t := range k.patternOrder {
		p := k.patterns[t]
		k.fact("names", t, p.pred)
		for _, v := range p.args {
			if v.kind == blankValue {
				k.fact("has the slot", t, v.text)
			}
		}
	}
}

func (k *knower) pattern(t string) (ast.PredicateSym, bool) {
	p, ok := k.patterns[t]
	if !ok {
		var err error
		if p, err = parsePattern(t); err != nil {
			return ast.PredicateSym{}, false
		}
	}
	return ast.PredicateSym{Symbol: mangleName(p.pred), Arity: len(p.args)}, true
}

func problemAtom(text string) ast.Atom {
	return ast.NewAtom("a_problem", ast.String(text))
}

func (k *knower) evaluate(returned []ast.Atom) *outcome {
	k.mu.Lock()
	problems := append([]string(nil), k.problems...)
	k.mu.Unlock()
	o := &outcome{problems: len(problems)}
	var clauses []ast.Clause
	for _, s := range k.statements {
		if s.usable {
			clauses = append(clauses, s.clause)
		}
	}
	for _, f := range k.facts {
		clauses = append(clauses, ast.Clause{Head: f})
	}
	for _, p := range problems {
		clauses = append(clauses, ast.Clause{Head: problemAtom(p)})
	}
	for _, f := range returned {
		clauses = append(clauses, ast.Clause{Head: f})
	}
	defined := map[ast.PredicateSym]bool{}
	for _, c := range clauses {
		defined[c.Head.Predicate] = true
	}
	extras := map[ast.PredicateSym]ast.Decl{}
	for _, c := range clauses {
		for _, p := range c.Premises {
			if a, ok := premiseAtom(p); ok && !defined[a.Predicate] {
				extras[a.Predicate] = ast.NewSyntheticDeclFromSym(a.Predicate)
			}
		}
	}
	info, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: clauses}, extras)
	if err != nil {
		o.err = err
		return o
	}
	o.store = factstore.NewSimpleInMemoryStore()
	rec := &recorder{events: map[string][]event{}}
	if err := engine.EvalProgram(info, o.store, engine.WithDerivationRecorder(rec)); err != nil {
		o.err = err
		return o
	}
	o.events = rec.events
	return o
}

func (o *outcome) get(sym ast.PredicateSym) []ast.Atom {
	var out []ast.Atom
	o.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
		out = append(out, a)
		return nil
	})
	return out
}

func (k *knower) all(o *outcome, pred string, arity int) []ast.Atom {
	return k.sorted(o.get(ast.PredicateSym{Symbol: mangleName(pred), Arity: arity}))
}

func (k *knower) rank(a ast.Atom) int {
	if n, ok := k.order[a.String()]; ok {
		return n
	}
	return len(k.statements)
}

func (k *knower) sorted(atoms []ast.Atom) []ast.Atom {
	sort.SliceStable(atoms, func(i, j int) bool {
		ri, rj := k.rank(atoms[i]), k.rank(atoms[j])
		if ri != rj {
			return ri < rj
		}
		return atoms[i].String() < atoms[j].String()
	})
	return atoms
}

func (k *knower) knowledgeOf(o *outcome) knowledge {
	return func(pred string) [][]string {
		var rows [][]string
		name := mangleName(pred)
		for _, sym := range o.store.ListPredicates() {
			if sym.Symbol != name {
				continue
			}
			for _, a := range k.sorted(o.get(sym)) {
				row := make([]string, len(a.Args))
				for i, t := range a.Args {
					row[i] = constText(t)
				}
				rows = append(rows, row)
			}
		}
		return rows
	}
}

type call struct {
	command string
	tool    string
	input   string
}

func (k *knower) run() *outcome {
	done := map[call]bool{}
	var returned []ast.Atom
	for round := 0; ; round++ {
		o := k.evaluate(returned)
		if o.err != nil {
			return o
		}
		var todo []call
		for _, a := range k.all(o, "calls", 3) {
			c := call{constText(a.Args[0]), constText(a.Args[1]), constText(a.Args[2])}
			if !done[c] {
				done[c] = true
				todo = append(todo, c)
			}
		}
		if len(todo) == 0 {
			return o
		}
		if round == maxRounds {
			k.addProblem(fmt.Sprintf("the commands kept coming for %d rounds", maxRounds))
			return k.evaluate(returned)
		}
		know := k.knowledgeOf(o)
		results := make([][]ast.Atom, len(todo))
		var wg sync.WaitGroup
		for i, c := range todo {
			wg.Add(1)
			go func() {
				defer wg.Done()
				out, err := runTool(c.tool, c.input, know)
				if err != nil {
					k.addProblem(fmt.Sprintf("%s calls %s with %s, which fails: %v", c.command, c.tool, c.input, err))
				}
				for _, r := range out {
					v := ast.BaseTerm(ast.String(r.text))
					if r.isNum {
						v = ast.Number(r.num)
					}
					results[i] = append(results[i], ast.NewAtom("returned", ast.String(c.command), ast.String(r.field), v))
				}
			}()
		}
		wg.Wait()
		for _, r := range results {
			returned = append(returned, r...)
		}
	}
}

func (k *knower) reasons(o *outcome, f ast.Atom) []string {
	var out []string
	seen := map[string]bool{}
	for _, ev := range o.events[f.String()] {
		var parts []string
		for _, p := range ev.clause.Premises {
			s, err := k.plainPremise(p.ApplySubst(ev.subst))
			if err != nil {
				parts = nil
				break
			}
			parts = append(parts, s)
		}
		if r := strings.Join(parts, " and "); r != "" && !seen[r] {
			seen[r] = true
			out = append(out, r)
		}
	}
	if file, ok := k.written[f.String()]; ok {
		out = append(out, "it is written in "+file)
	}
	return out
}

func (k *knower) finish(o *outcome) int {
	if o.err != nil {
		k.addProblem(fmt.Sprintf("mangle can't evaluate the knowledge: %v", o.err))
		return k.fallback()
	}
	var views []string
	printed := map[string]bool{}
	for _, a := range k.all(o, "prints", 2) {
		if v := constText(a.Args[1]); constText(a.Args[0]) == machine && !printed[v] {
			printed[v] = true
			views = append(views, v)
		}
	}
	for _, a := range k.all(o, "prints in", 2) {
		if l := constText(a.Args[1]); constText(a.Args[0]) == machine && l != "plain language" {
			k.addProblem(fmt.Sprintf("engine.go can't print in %s", l))
		}
	}
	for _, a := range k.all(o, "prints to", 2) {
		if p := constText(a.Args[1]); constText(a.Args[0]) == machine && p != "standard output" {
			k.addProblem(fmt.Sprintf("engine.go can't print to %s", p))
		}
	}
	for _, a := range k.all(o, "gives reasons for", 2) {
		sym, ok := k.pattern(constText(a.Args[1]))
		if !ok || !printed[constText(a.Args[0])] {
			continue
		}
		for _, f := range o.get(sym) {
			plain, err := k.plainAtom(f)
			if err != nil {
				continue
			}
			for _, r := range k.reasons(o, f) {
				o.store.Add(ast.NewAtom("holds_because", ast.String(plain), ast.String(r)))
			}
		}
	}
	code := k.answer(o)
	k.mu.Lock()
	for _, p := range k.problems[o.problems:] {
		o.store.Add(problemAtom(p))
	}
	k.mu.Unlock()
	k.print(o, views)
	return code
}

func (k *knower) exitCode(o *outcome, answer string) (int, bool) {
	for _, a := range k.all(o, "exits with", 2) {
		if c, ok := a.Args[1].(ast.Constant); ok && constText(a.Args[0]) == answer && c.Type == ast.NumberType {
			return int(c.NumValue), true
		}
	}
	return 0, false
}

func (k *knower) answer(o *outcome) int {
	answer := brokenAnswer
	k.mu.Lock()
	fresh := len(k.problems) > o.problems
	k.mu.Unlock()
	if len(k.all(o, "a problem", 1)) == 0 && !fresh {
		var answers []string
		for _, a := range k.all(o, "conforms", 2) {
			if constText(a.Args[0]) == theFolder {
				answers = append(answers, constText(a.Args[1]))
			}
		}
		if len(answers) == 1 {
			answer = answers[0]
		} else {
			k.addProblem(fmt.Sprintf("the folder conforms in %d ways, not in one", len(answers)))
		}
	}
	if code, ok := k.exitCode(o, answer); ok {
		return code
	}
	k.addProblem(fmt.Sprintf("nothing says what %s exits with", answer))
	if code, ok := k.exitCode(o, brokenAnswer); ok {
		return code
	}
	return 2
}

func (k *knower) shown(o *outcome, view string) []ast.PredicateSym {
	explicit := map[string]int{}
	for i, s := range k.statements {
		h := s.head
		if !s.translated || len(s.conds) > 0 || h.verb != "shows" || len(h.args) != 2 {
			continue
		}
		if h.args[0].kind == textValue && h.args[0].text == view && h.args[1].kind == textValue {
			if _, ok := explicit[h.args[1].text]; !ok {
				explicit[h.args[1].text] = i
			}
		}
	}
	seenAt := map[string]int{}
	for i, t := range k.patternOrder {
		seenAt[t] = i
	}
	key := func(t string) (int, int) {
		if n, ok := explicit[t]; ok {
			return 1, n
		}
		if n, ok := seenAt[t]; ok {
			return 0, n
		}
		return 0, len(k.patternOrder)
	}
	var patterns []string
	for _, a := range k.all(o, "shows", 2) {
		if constText(a.Args[0]) == view {
			patterns = append(patterns, constText(a.Args[1]))
		}
	}
	sort.SliceStable(patterns, func(i, j int) bool {
		gi, ni := key(patterns[i])
		gj, nj := key(patterns[j])
		if gi != gj {
			return gi < gj
		}
		if ni != nj {
			return ni < nj
		}
		return patterns[i] < patterns[j]
	})
	var syms []ast.PredicateSym
	seen := map[ast.PredicateSym]bool{}
	for _, t := range patterns {
		if sym, ok := k.pattern(t); ok && !seen[sym] {
			seen[sym] = true
			syms = append(syms, sym)
		}
	}
	return syms
}

func (k *knower) print(o *outcome, views []string) {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for _, view := range views {
		if view == knowledgeView {
			in := map[string]bool{}
			for _, a := range k.all(o, "in the knowledge view", 1) {
				in[constText(a.Args[0])] = true
			}
			done := map[string]bool{}
			for _, s := range k.statements {
				if !s.translated || !in[s.id] || done[s.id] {
					continue
				}
				done[s.id] = true
				text := s.readBack
				if text == "" {
					text = strings.Join(s.lines, "\n")
				}
				fmt.Fprintln(w, text)
			}
			fmt.Fprintln(w)
		}
		for _, sym := range k.shown(o, view) {
			type line struct {
				rank int
				text string
			}
			var lines []line
			for _, a := range o.get(sym) {
				if s, err := k.plainAtom(a); err == nil {
					lines = append(lines, line{k.rank(a), s})
				}
			}
			sort.Slice(lines, func(i, j int) bool {
				if lines[i].rank != lines[j].rank {
					return lines[i].rank < lines[j].rank
				}
				return lines[i].text < lines[j].text
			})
			for _, l := range lines {
				fmt.Fprintln(w, l.text)
			}
		}
	}
}

func (k *knower) fallback() int {
	w := bufio.NewWriter(os.Stdout)
	for _, p := range k.problems {
		fmt.Fprintln(w, plainText(p)+", is, a problem")
	}
	w.Flush()
	for _, s := range k.statements {
		h := s.head
		if !s.translated || len(s.conds) > 0 || h.verb != "exits with" || len(h.args) != 2 {
			continue
		}
		if h.args[0].kind == textValue && h.args[0].text == brokenAnswer && h.args[1].kind == numberValue {
			return int(h.args[1].num)
		}
	}
	return 2
}
