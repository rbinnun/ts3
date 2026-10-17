package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/unionfind"
)

const (
	engineFile      = "engine.go"
	firstFile       = "spec.plain"
	changeSignal    = "THIS_RUN_IS_A_CHANGE"
	lawVerb         = "breaks"
	reasonVerb      = "holds because"
	patternVariable = "fact pattern"
	plainLanguage   = "plain language"
	standardOutput  = "standard output"
	brokenAnswer    = "broken"
	brokenFallback  = 2
	roundLimit      = 200
	factLimit       = 1000000
)

var engineInstructions = map[string]int{
	"loads":             2,
	"means in mangle":   2,
	"uses":              3,
	"exits with":        2,
	"conforms":          2,
	"a problem":         1,
	"prints":            2,
	"prints in":         2,
	"prints to":         2,
	"shows":             2,
	"gives reasons for": 2,
	"creates fact":      2,
}

var builtinVerbs = map[string]string{
	"ends with":      ":string:ends_with",
	"starts with":    ":string:starts_with",
	"differs from":   "!=",
	"is the join of": "fn:string:concat",
}

var builtinWords = map[string]string{
	":string:ends_with":   "ends with",
	":string:starts_with": "starts with",
}

var (
	variableForm = regexp.MustCompile(`^\[([a-z][a-z0-9]*(?: [a-z][a-z0-9]*)*)\]$`)
	bracketForm  = regexp.MustCompile(`^\[[^\[\]]*\]$`)
	numberForm   = regexp.MustCompile(`^-?[0-9]+$`)
	wordsForm    = regexp.MustCompile(`^[a-z]+(?: [a-z]+)*$`)
	sentencePart = regexp.MustCompile(`\[[^\[\]]*\]|[^\[\]]+`)
)

type piece struct {
	text   string
	quoted bool
}

type literal struct {
	negated bool
	builtin string
	name    string
	args    []ast.BaseTerm
}

type chunk struct {
	line        int
	lines       []string
	blankBefore bool
}

type trouble struct {
	line int
	text string
}

type rule struct {
	id          string
	file        string
	index       int
	lines       []string
	clause      ast.Clause
	blankBefore bool
	bad         bool
}

type baseFact struct {
	atom    ast.Atom
	creator string
}

type command struct {
	name  string
	tool  string
	input string
}

type firing struct {
	rule  ast.Clause
	head  ast.Atom
	subst unionfind.UnionFind
}

type recorder struct {
	wanted  map[ast.PredicateSym]bool
	firings []firing
}

func (r *recorder) RuleFired(rule ast.Clause, head ast.Atom, subst unionfind.UnionFind, _ []ast.Atom) {
	if r.wanted[head.Predicate] {
		r.firings = append(r.firings, firing{rule: rule, head: head, subst: subst})
	}
}

func (r *recorder) LetEmit(ast.Clause, ast.Atom, ast.ConstSubstList, ast.Atom) {}

func (r *recorder) DoEmit(ast.Clause, ast.Atom, []ast.Constant, []ast.Atom, ast.Atom) {}

type statedFact struct {
	atom ast.Atom
	ids  []string
}

type place struct {
	pred  ast.PredicateSym
	index int
}

type machine struct {
	folder      string
	loaded      map[string]bool
	rules       []*rule
	factAt      map[string]int
	firstSeen   map[string]int
	base        map[string]baseFact
	dirty       bool
	store       factstore.FactStore
	firings     []firing
	ruleOf      map[string]*rule
	stated      map[string]*statedFact
	reasonPreds map[ast.PredicateSym]bool
	reasonRank  map[string]int
	executed    map[string]command
	named       map[string]bool
}

func main() {
	m := newMachine(".")
	if os.Getenv(changeSignal) != "" {
		m.create(engineFile, fact("this run is a change"))
	}
	m.load(firstFile, true)
	m.run()
	out := bufio.NewWriter(os.Stdout)
	printed := m.printViews(out)
	out.Flush()
	if !printed {
		for _, p := range m.problems() {
			fmt.Fprintln(os.Stderr, p)
		}
	}
	os.Exit(m.exitCode())
}

func newMachine(folder string) *machine {
	return &machine{
		folder:      folder,
		loaded:      map[string]bool{},
		factAt:      map[string]int{},
		firstSeen:   map[string]int{},
		base:        map[string]baseFact{},
		ruleOf:      map[string]*rule{},
		stated:      map[string]*statedFact{},
		reasonPreds: map[ast.PredicateSym]bool{},
		executed:    map[string]command{},
		named:       map[string]bool{},
	}
}

func mangleName(words string) string {
	return strings.ReplaceAll(words, " ", "_")
}

func plainName(symbol string) string {
	return strings.ReplaceAll(symbol, "_", " ")
}

func variableName(words string) string {
	var b strings.Builder
	for _, w := range strings.Fields(words) {
		r, size := utf8.DecodeRuneInString(w)
		b.WriteRune(unicode.ToUpper(r))
		b.WriteString(w[size:])
	}
	return b.String()
}

func variableWords(symbol string) string {
	var words []string
	var current []rune
	for _, r := range symbol {
		if unicode.IsUpper(r) && len(current) > 0 {
			words = append(words, string(current))
			current = nil
		}
		current = append(current, unicode.ToLower(r))
	}
	if len(current) > 0 {
		words = append(words, string(current))
	}
	return strings.Join(words, " ")
}

func fact(words string, args ...ast.BaseTerm) ast.Atom {
	return ast.NewAtom(mangleName(words), args...)
}

func str(s string) ast.BaseTerm {
	return ast.String(s)
}

func text(c ast.Constant) (string, bool) {
	if c.Type != ast.StringType {
		return "", false
	}
	return c.Symbol, true
}

func valueText(c ast.Constant) string {
	if s, ok := text(c); ok {
		return s
	}
	if c.Type == ast.NumberType {
		return strconv.FormatInt(c.NumValue, 10)
	}
	return c.String()
}

func splitTerms(line string) ([]piece, error) {
	var toks []piece
	i := 0
	for {
		if i < len(line) && (line[i] == '"' || line[i] == '\'') {
			q := line[i]
			i++
			var b strings.Builder
			closed := false
			for i < len(line) {
				if line[i] == q {
					if i+1 < len(line) && line[i+1] == q {
						b.WriteByte(q)
						i += 2
						continue
					}
					i++
					closed = true
					break
				}
				b.WriteByte(line[i])
				i++
			}
			if !closed {
				return nil, errors.New("a quote is never closed")
			}
			toks = append(toks, piece{text: b.String(), quoted: true})
			if i == len(line) {
				return toks, nil
			}
			if !strings.HasPrefix(line[i:], ", ") {
				return nil, errors.New("a quoted term must be followed by a comma and a space")
			}
			i += 2
			continue
		}
		j := strings.Index(line[i:], ", ")
		if j < 0 {
			toks = append(toks, piece{text: line[i:]})
			return toks, nil
		}
		toks = append(toks, piece{text: line[i : i+j]})
		i += j + 2
	}
}

func termOf(t piece) (ast.BaseTerm, error) {
	if t.quoted {
		return ast.String(t.text), nil
	}
	if t.text == "" {
		return nil, errors.New("a term is empty")
	}
	if found := variableForm.FindStringSubmatch(t.text); found != nil {
		return ast.Variable{Symbol: variableName(found[1])}, nil
	}
	if bracketForm.MatchString(t.text) {
		return nil, fmt.Errorf("%s is not a variable, because a variable is lowercase words in brackets", t.text)
	}
	if numberForm.MatchString(t.text) {
		n, err := strconv.ParseInt(t.text, 10, 64)
		if err != nil {
			return nil, fmt.Errorf("%s is too large a number", t.text)
		}
		return ast.Number(n), nil
	}
	return ast.String(t.text), nil
}

func literalOf(toks []piece, condition bool) (literal, error) {
	if len(toks) == 1 {
		if !wordsForm.MatchString(toks[0].text) {
			return literal{}, errors.New("a line with one term must be lowercase words")
		}
		return literal{name: mangleName(toks[0].text)}, nil
	}
	if len(toks) == 2 {
		return literal{}, errors.New("a line needs one term or at least three, and this one has two")
	}
	verb := toks[1].text
	if !wordsForm.MatchString(verb) {
		return literal{}, fmt.Errorf("%q is not a verb in lowercase words", verb)
	}
	var args []ast.BaseTerm
	for i, t := range toks {
		if i == 1 {
			continue
		}
		term, err := termOf(t)
		if err != nil {
			return literal{}, err
		}
		args = append(args, term)
	}
	if verb == "is" && len(toks) == 3 {
		if !wordsForm.MatchString(toks[2].text) {
			return literal{}, fmt.Errorf("%q is not a description in lowercase words", toks[2].text)
		}
		return literal{name: mangleName(toks[2].text), args: args[:1]}, nil
	}
	if _, ok := builtinVerbs[verb]; ok {
		if !condition {
			return literal{}, fmt.Errorf("%q can only be a condition", verb)
		}
		if verb == "is the join of" {
			if len(args) < 3 {
				return literal{}, errors.New("a join needs at least two parts")
			}
		} else if len(args) != 2 {
			return literal{}, fmt.Errorf("%q takes exactly two terms", verb)
		}
		return literal{builtin: verb, args: args}, nil
	}
	return literal{name: mangleName(verb), args: args}, nil
}

func (l literal) atom() ast.Atom {
	return ast.Atom{Predicate: ast.PredicateSym{Symbol: l.name, Arity: len(l.args)}, Args: l.args}
}

func (l literal) ground() bool {
	if l.builtin != "" {
		return false
	}
	for _, a := range l.args {
		if _, ok := a.(ast.Constant); !ok {
			return false
		}
	}
	return true
}

func (l literal) mangle() string {
	terms := make([]string, len(l.args))
	for i, a := range l.args {
		terms[i] = a.String()
	}
	var s string
	switch l.builtin {
	case "":
		s = l.name + "(" + strings.Join(terms, ", ") + ")"
	case "differs from":
		s = terms[0] + " != " + terms[1]
	case "is the join of":
		s = terms[0] + " = " + builtinVerbs[l.builtin] + "(" + strings.Join(terms[1:], ", ") + ")"
	default:
		s = builtinVerbs[l.builtin] + "(" + strings.Join(terms, ", ") + ")"
	}
	if l.negated {
		s = "!" + s
	}
	return s
}

func lineLiteral(line string, condition bool) (literal, error) {
	toks, err := splitTerms(line)
	if err != nil {
		return literal{}, fmt.Errorf("%q: %v", line, err)
	}
	lit, err := literalOf(toks, condition)
	if err != nil {
		return literal{}, fmt.Errorf("%q: %v", line, err)
	}
	return lit, nil
}

func mangleClause(lines []string) (string, error) {
	head, err := lineLiteral(lines[0], false)
	if err != nil {
		return "", err
	}
	text := head.mangle()
	for i, l := range lines[1:] {
		body := strings.TrimLeft(l, " \t")
		switch {
		case strings.HasPrefix(body, "if "):
			body = body[len("if "):]
		case strings.HasPrefix(body, "and "):
			body = body[len("and "):]
		default:
			return "", fmt.Errorf("%q should begin with if or and", l)
		}
		negated := strings.HasPrefix(body, "not ")
		if negated {
			body = body[len("not "):]
		}
		lit, err := lineLiteral(body, true)
		if err != nil {
			return "", err
		}
		if negated {
			if lit.builtin != "" {
				return "", fmt.Errorf("%q cannot follow not", body)
			}
			lit.negated = true
		}
		if i == 0 {
			text += " :- "
		} else {
			text += ", "
		}
		text += lit.mangle()
	}
	return text + ".", nil
}

func plainMeaning(plain string) (string, error) {
	lit, err := lineLiteral(plain, true)
	if err != nil {
		return "", err
	}
	if lit.builtin != "" {
		return lit.mangle(), nil
	}
	return lit.mangle() + ".", nil
}

func needsQuotes(s string, first bool) bool {
	if s == "" || strings.Contains(s, ", ") {
		return true
	}
	r0, _ := utf8.DecodeRuneInString(s)
	rl, _ := utf8.DecodeLastRuneInString(s)
	if unicode.IsSpace(r0) || unicode.IsSpace(rl) || r0 == '"' || r0 == '\'' {
		return true
	}
	if bracketForm.MatchString(s) || numberForm.MatchString(s) {
		return true
	}
	return first && strings.HasPrefix(s, "not ")
}

func plainString(s string, first bool) string {
	s = strings.ReplaceAll(s, "\r", `\r`)
	s = strings.ReplaceAll(s, "\n", `\n`)
	if !needsQuotes(s, first) {
		return s
	}
	if !strings.Contains(s, `"`) {
		return `"` + s + `"`
	}
	if !strings.Contains(s, "'") {
		return "'" + s + "'"
	}
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func plainTerm(t ast.BaseTerm, first bool) string {
	switch t := t.(type) {
	case ast.Variable:
		return "[" + variableWords(t.Symbol) + "]"
	case ast.Constant:
		switch t.Type {
		case ast.StringType:
			return plainString(t.Symbol, first)
		case ast.NumberType:
			return strconv.FormatInt(t.NumValue, 10)
		}
		return t.String()
	}
	return t.String()
}

func plainAtom(a ast.Atom, condition bool) string {
	words := plainName(a.Predicate.Symbol)
	switch len(a.Args) {
	case 0:
		return words
	case 1:
		return plainTerm(a.Args[0], condition) + ", is, " + words
	}
	s := plainTerm(a.Args[0], condition) + ", " + words
	for _, t := range a.Args[1:] {
		s += ", " + plainTerm(t, false)
	}
	return s
}

func plainPremise(p ast.Term) string {
	switch p := p.(type) {
	case ast.Atom:
		if words, ok := builtinWords[p.Predicate.Symbol]; ok && len(p.Args) == 2 {
			return plainTerm(p.Args[0], true) + ", " + words + ", " + plainTerm(p.Args[1], false)
		}
		return plainAtom(p, true)
	case ast.NegAtom:
		return "not " + plainAtom(p.Atom, true)
	case ast.Ineq:
		return plainTerm(p.Left, true) + ", differs from, " + plainTerm(p.Right, false)
	case ast.Eq:
		if f, ok := p.Right.(ast.ApplyFn); ok && f.Function.Symbol == builtinVerbs["is the join of"] {
			s := plainTerm(p.Left, true) + ", is the join of"
			for _, a := range f.Args {
				s += ", " + plainTerm(a, false)
			}
			return s
		}
	}
	return p.String()
}

func plainClause(c ast.Clause) []string {
	lines := []string{plainAtom(c.Head, false)}
	for i, p := range c.Premises {
		lead := "    and "
		if i == 0 {
			lead = "    if "
		}
		lines = append(lines, lead+plainPremise(p))
	}
	return lines
}

func sentenceLine(s string) (string, error) {
	var toks []string
	for _, part := range sentencePart.FindAllString(s, -1) {
		if strings.HasPrefix(part, "[") {
			if !variableForm.MatchString(part) {
				return "", fmt.Errorf("%s is not a variable", part)
			}
			toks = append(toks, part)
			continue
		}
		words := strings.TrimSpace(part)
		if words == "" {
			continue
		}
		if !wordsForm.MatchString(words) {
			return "", fmt.Errorf("%q is not lowercase words", words)
		}
		toks = append(toks, words)
	}
	if strings.Join(toks, " ") != s {
		return "", errors.New("it is not words and variables with single spaces between them")
	}
	isVar := func(t string) bool { return strings.HasPrefix(t, "[") }
	switch {
	case len(toks) == 1 && !isVar(toks[0]):
		return toks[0], nil
	case len(toks) == 2 && isVar(toks[0]) && strings.HasPrefix(toks[1], "is "):
		return toks[0] + ", is, " + strings.TrimPrefix(toks[1], "is "), nil
	case len(toks) >= 3 && isVar(toks[0]) && !isVar(toks[1]):
		for _, t := range toks[2:] {
			if !isVar(t) {
				return "", errors.New("only variables may follow the verb")
			}
		}
		return strings.Join(toks, ", "), nil
	}
	return "", errors.New("it does not have the shape of a fact")
}

func patternLiteral(s string) (literal, error) {
	line, err := sentenceLine(s)
	if err != nil {
		return literal{}, err
	}
	return lineLiteral(line, false)
}

func chunksOf(text string) ([]chunk, []trouble) {
	lines := strings.Split(text, "\n")
	if n := len(lines); n > 0 && lines[n-1] == "" {
		lines = lines[:n-1]
	}
	var chunks []chunk
	var troubles []trouble
	blank, open := false, false
	for i, l := range lines {
		switch {
		case strings.TrimSpace(l) == "":
			blank, open = true, false
		case l[0] == ' ' || l[0] == '\t':
			if !open {
				troubles = append(troubles, trouble{line: i + 1, text: fmt.Sprintf("%q is a condition with no rule above it", l)})
				continue
			}
			last := &chunks[len(chunks)-1]
			last.lines = append(last.lines, l)
		default:
			chunks = append(chunks, chunk{line: i + 1, lines: []string{l}, blankBefore: blank})
			blank, open = false, true
		}
	}
	return chunks, troubles
}

func (m *machine) create(creator string, a ast.Atom) bool {
	key := a.String()
	if _, ok := m.base[key]; ok {
		return false
	}
	m.base[key] = baseFact{atom: a, creator: creator}
	m.dirty = true
	return true
}

func (m *machine) problem(text string) {
	m.create(engineFile, fact("a problem", str(text)))
}

func (m *machine) problems() []string {
	var out []string
	for _, b := range m.base {
		if b.atom.Predicate.Symbol == mangleName("a problem") && len(b.atom.Args) == 1 {
			if c, ok := b.atom.Args[0].(ast.Constant); ok {
				out = append(out, valueText(c))
			}
		}
	}
	sort.Strings(out)
	return out
}

func (m *machine) load(name string, required bool) {
	if m.loaded[name] {
		return
	}
	m.loaded[name] = true
	m.dirty = true
	if !filepath.IsLocal(name) {
		m.problem(fmt.Sprintf("%s is not a file in the folder", name))
		return
	}
	data, err := os.ReadFile(filepath.Join(m.folder, filepath.FromSlash(name)))
	if errors.Is(err, fs.ErrNotExist) && !required {
		return
	}
	if err != nil {
		m.problem(fmt.Sprintf("%s cannot be read: %v", name, err))
		return
	}
	chunks, troubles := chunksOf(string(data))
	for _, t := range troubles {
		m.problem(fmt.Sprintf("%s:%d: %s", name, t.line, t.text))
	}
	for _, c := range chunks {
		m.addRule(name, c)
	}
}

func (m *machine) addRule(file string, c chunk) {
	text, err := mangleClause(c.lines)
	if err != nil {
		m.problem(fmt.Sprintf("%s:%d: %v", file, c.line, err))
		return
	}
	clause, err := parse.Clause(text)
	if err != nil {
		m.problem(fmt.Sprintf("%s:%d: mangle cannot read %s: %v", file, c.line, text, err))
		return
	}
	r := &rule{
		id:          fmt.Sprintf("%s:%d", file, c.line),
		file:        file,
		index:       len(m.rules),
		lines:       c.lines,
		clause:      clause,
		blankBefore: c.blankBefore,
	}
	m.rules = append(m.rules, r)
	written := plainClause(clause)
	for i, l := range c.lines {
		if i >= len(written) || written[i] != l {
			m.create(engineFile, fact("misread", str(l)))
		}
	}
	if len(clause.Premises) == 0 {
		if _, ok := m.factAt[clause.Head.String()]; !ok {
			m.factAt[clause.Head.String()] = r.index
		}
	}
	m.noteStrings(clause)
	head := plainName(clause.Head.Predicate.Symbol)
	m.create(engineFile, fact("has a rule for", str(file), str(head)))
	m.create(engineFile, fact("defines", str(r.id), str(head)))
	for _, p := range clause.Premises {
		if a, ok := atomOf(p); ok {
			m.create(engineFile, fact("refers to", str(r.id), str(plainName(a.Predicate.Symbol))))
		}
	}
	if clause.Head.Predicate.Symbol == mangleName(lawVerb) && len(clause.Head.Args) == 2 {
		if law, ok := clause.Head.Args[1].(ast.Constant); ok {
			m.create(engineFile, fact("lays down", str(r.id), law))
		}
	}
}

func atomOf(p ast.Term) (ast.Atom, bool) {
	switch p := p.(type) {
	case ast.Atom:
		return p, !p.Predicate.IsBuiltin()
	case ast.NegAtom:
		return p.Atom, !p.Atom.Predicate.IsBuiltin()
	}
	return ast.Atom{}, false
}

func (m *machine) noteStrings(c ast.Clause) {
	var note func(t ast.BaseTerm)
	note = func(t ast.BaseTerm) {
		switch t := t.(type) {
		case ast.Constant:
			if s, ok := text(t); ok {
				if _, seen := m.firstSeen[s]; !seen {
					m.firstSeen[s] = len(m.firstSeen)
				}
			}
		case ast.ApplyFn:
			for _, a := range t.Args {
				note(a)
			}
		}
	}
	terms := append([]ast.BaseTerm{}, c.Head.Args...)
	for _, p := range c.Premises {
		switch p := p.(type) {
		case ast.Atom:
			terms = append(terms, p.Args...)
		case ast.NegAtom:
			terms = append(terms, p.Atom.Args...)
		case ast.Eq:
			terms = append(terms, p.Left, p.Right)
		case ast.Ineq:
			terms = append(terms, p.Left, p.Right)
		}
	}
	for _, t := range terms {
		note(t)
	}
}

func (m *machine) ordered(values []string) []string {
	out := append([]string{}, values...)
	sort.SliceStable(out, func(i, j int) bool {
		a, aok := m.firstSeen[out[i]]
		b, bok := m.firstSeen[out[j]]
		switch {
		case aok && bok:
			return a < b
		case aok != bok:
			return aok
		}
		return out[i] < out[j]
	})
	return out
}

func rowKey(row []ast.Constant) string {
	parts := make([]string, len(row))
	for i, c := range row {
		parts[i] = c.String()
	}
	return strings.Join(parts, "\x00")
}

func (m *machine) rowsOf(p ast.PredicateSym) [][]ast.Constant {
	if m.store == nil {
		return nil
	}
	args := make([]ast.BaseTerm, p.Arity)
	for i := range args {
		args[i] = ast.Variable{Symbol: "X" + strconv.Itoa(i)}
	}
	var out [][]ast.Constant
	_ = m.store.GetFacts(ast.Atom{Predicate: p, Args: args}, func(a ast.Atom) error {
		row := make([]ast.Constant, len(a.Args))
		for i, t := range a.Args {
			c, ok := t.(ast.Constant)
			if !ok {
				return nil
			}
			row[i] = c
		}
		out = append(out, row)
		return nil
	})
	sort.Slice(out, func(i, j int) bool { return rowKey(out[i]) < rowKey(out[j]) })
	return out
}

func (m *machine) rows(words string, arity int) [][]ast.Constant {
	return m.rowsOf(ast.PredicateSym{Symbol: mangleName(words), Arity: arity})
}

func (m *machine) about(words string, arity int, subject string) []ast.Constant {
	var out []ast.Constant
	for _, row := range m.rows(words, arity) {
		if s, ok := text(row[0]); ok && s == subject {
			out = append(out, row[1:]...)
		}
	}
	return out
}

func (m *machine) holds(a ast.Atom) bool {
	return m.store != nil && m.store.Contains(a)
}

func (m *machine) run() {
	for round := 0; ; round++ {
		if round == roundLimit {
			m.problem(fmt.Sprintf("the folder does not settle after %d rounds", roundLimit))
			m.evaluate()
			return
		}
		m.dirty = false
		m.evaluate()
		if m.followLoads(); m.dirty {
			continue
		}
		if m.namePatterns(); m.dirty {
			continue
		}
		if m.runCommands(); m.dirty {
			continue
		}
		m.settle()
		if !m.dirty {
			return
		}
	}
}

func analyze(clauses []ast.Clause) (*analysis.ProgramInfo, error) {
	defined := map[ast.PredicateSym]bool{}
	for _, c := range clauses {
		defined[c.Head.Predicate] = true
	}
	given := map[ast.PredicateSym]ast.Decl{}
	for _, c := range clauses {
		for _, p := range c.Premises {
			if a, ok := atomOf(p); ok && !defined[a.Predicate] {
				given[a.Predicate] = ast.NewSyntheticDeclFromSym(a.Predicate)
			}
		}
	}
	a, err := analysis.New(given, nil, analysis.NoBoundsChecking)
	if err != nil {
		return nil, err
	}
	return a.Analyze(clauses)
}

func arityClash(c ast.Clause, arity map[string]int) string {
	atoms := []ast.Atom{c.Head}
	for _, p := range c.Premises {
		if a, ok := atomOf(p); ok {
			atoms = append(atoms, a)
		}
	}
	for _, a := range atoms {
		if n, ok := arity[a.Predicate.Symbol]; ok && n != a.Predicate.Arity {
			return fmt.Sprintf("%q has %d terms here and %d elsewhere", plainName(a.Predicate.Symbol), a.Predicate.Arity, n)
		}
	}
	for _, a := range atoms {
		arity[a.Predicate.Symbol] = a.Predicate.Arity
	}
	return ""
}

func (m *machine) program() []*rule {
	arity := map[string]int{}
	for _, b := range m.base {
		arity[b.atom.Predicate.Symbol] = b.atom.Predicate.Arity
	}
	var kept []*rule
	for _, r := range m.rules {
		if r.bad {
			continue
		}
		if why := arityClash(r.clause, arity); why != "" {
			r.bad = true
			m.problem(fmt.Sprintf("%s: %s", r.id, why))
			continue
		}
		kept = append(kept, r)
	}
	if _, err := analyze(clausesOf(kept)); err == nil {
		return kept
	}
	var safe []*rule
	for _, r := range kept {
		if _, err := analyze([]ast.Clause{r.clause}); err != nil {
			r.bad = true
			m.problem(fmt.Sprintf("%s: %v", r.id, err))
			continue
		}
		safe = append(safe, r)
	}
	return safe
}

func clausesOf(rules []*rule) []ast.Clause {
	out := make([]ast.Clause, len(rules))
	for i, r := range rules {
		out[i] = r.clause
	}
	return out
}

func (m *machine) solve(rules []*rule) (factstore.FactStore, []firing, map[string]*rule, error) {
	info, err := analyze(clausesOf(rules))
	if err != nil {
		return nil, nil, nil, fmt.Errorf("the rules cannot be read together: %v", err)
	}
	strata, order, err := analysis.Stratify(analysis.Program{
		EdbPredicates: info.EdbPredicates,
		IdbPredicates: info.IdbPredicates,
		Rules:         info.Rules,
	})
	if err != nil {
		return nil, nil, nil, fmt.Errorf("the rules cannot be put in order: %v", err)
	}
	ruleOf := map[string]*rule{}
	i := 0
	for _, r := range rules {
		if len(r.clause.Premises) == 0 {
			continue
		}
		if i < len(info.Rules) {
			if _, ok := ruleOf[info.Rules[i].String()]; !ok {
				ruleOf[info.Rules[i].String()] = r
			}
		}
		i++
	}
	store := factstore.NewSimpleInMemoryStore()
	for _, b := range m.base {
		store.Add(b.atom)
	}
	rec := &recorder{wanted: m.reasonPreds}
	_, err = engine.EvalStratifiedProgramWithStats(info, strata, order, store,
		engine.WithDerivationRecorder(rec), engine.WithCreatedFactLimit(factLimit))
	if err != nil {
		return nil, nil, nil, fmt.Errorf("the rules cannot be worked out: %v", err)
	}
	return store, rec.firings, ruleOf, nil
}

func (m *machine) evaluate() {
	rules := m.program()
	store, firings, ruleOf, err := m.solve(rules)
	if err != nil {
		m.problem(err.Error())
		var facts []*rule
		for _, r := range rules {
			if len(r.clause.Premises) == 0 {
				facts = append(facts, r)
			}
		}
		rules = facts
		store, firings, ruleOf, err = m.solve(rules)
		if err != nil {
			m.problem(err.Error())
			rules = nil
			plain := factstore.NewSimpleInMemoryStore()
			for _, b := range m.base {
				plain.Add(b.atom)
			}
			store, firings, ruleOf = plain, nil, map[string]*rule{}
		}
	}
	m.store, m.firings, m.ruleOf = store, firings, ruleOf
	m.stated = map[string]*statedFact{}
	for _, r := range rules {
		if len(r.clause.Premises) > 0 {
			continue
		}
		key := r.clause.Head.String()
		if m.stated[key] == nil {
			m.stated[key] = &statedFact{atom: r.clause.Head}
		}
		m.stated[key].ids = append(m.stated[key].ids, r.id)
	}
}

func (m *machine) followLoads() {
	var files []string
	for _, f := range m.about("loads", 2, engineFile) {
		name, ok := text(f)
		if !ok {
			m.problem(fmt.Sprintf("%s cannot load %s, which is not a file name", engineFile, f.String()))
			continue
		}
		files = append(files, name)
	}
	for _, name := range m.ordered(files) {
		m.load(name, false)
	}
}

func (m *machine) patternPlaces() []place {
	seen := map[place]bool{}
	var out []place
	want := variableName(patternVariable)
	add := func(a ast.Atom) {
		for i, t := range a.Args {
			if v, ok := t.(ast.Variable); ok && v.Symbol == want {
				p := place{pred: a.Predicate, index: i}
				if !seen[p] {
					seen[p] = true
					out = append(out, p)
				}
			}
		}
	}
	for _, r := range m.rules {
		if r.bad {
			continue
		}
		add(r.clause.Head)
		for _, p := range r.clause.Premises {
			if a, ok := atomOf(p); ok {
				add(a)
			}
		}
	}
	for _, row := range m.rows("executes instruction", 2) {
		if s, ok := text(row[1]); ok {
			if lit, err := patternLiteral(s); err == nil {
				add(lit.atom())
			}
		}
	}
	return out
}

func (m *machine) namePatterns() {
	for _, at := range m.patternPlaces() {
		for _, row := range m.rowsOf(at.pred) {
			key := row[at.index].String()
			if m.named[key] {
				continue
			}
			m.named[key] = true
			s, ok := text(row[at.index])
			if !ok {
				m.problem(fmt.Sprintf("%s is not a fact pattern", key))
				continue
			}
			lit, err := patternLiteral(s)
			if err != nil {
				m.problem(fmt.Sprintf("%q is not a fact pattern: %v", s, err))
				continue
			}
			m.create(engineFile, fact("names", str(s), str(plainName(lit.name))))
		}
	}
}

func commandKey(c command) string {
	return c.name + "\x00" + c.tool + "\x00" + c.input
}

func (m *machine) runCommands() {
	var batch []command
	for _, row := range m.rows("uses", 3) {
		name, ok1 := text(row[0])
		tool, ok2 := text(row[1])
		input, ok3 := text(row[2])
		if !ok1 || !ok2 || !ok3 {
			m.problem(fmt.Sprintf("%s, uses, %s, %s cannot be carried out", row[0].String(), row[1].String(), row[2].String()))
			continue
		}
		c := command{name: name, tool: tool, input: input}
		if _, done := m.executed[commandKey(c)]; done {
			continue
		}
		m.executed[commandKey(c)] = c
		batch = append(batch, c)
	}
	if len(batch) == 0 {
		return
	}
	for i, err := range m.useTools(batch) {
		if err != nil {
			m.problem(fmt.Sprintf("%s could not use %s on %s: %v", batch[i].name, batch[i].tool, batch[i].input, err))
		}
	}
	m.dirty = true
}

func (m *machine) settle() {
	m.updateReasonPreds()
	m.giveReasons()
	m.checkInstructions()
	m.checkCreations()
	m.checkMeanings()
	m.checkPrinting()
	m.checkCommands()
	m.checkAnswer()
}

func (m *machine) updateReasonPreds() {
	want := map[ast.PredicateSym]bool{}
	for _, row := range m.rows("gives reasons for", 2) {
		s, ok := text(row[1])
		if !ok {
			continue
		}
		if lit, err := patternLiteral(s); err == nil {
			want[lit.atom().Predicate] = true
		}
	}
	same := len(want) == len(m.reasonPreds)
	for p := range want {
		if !m.reasonPreds[p] {
			same = false
		}
	}
	if !same {
		m.reasonPreds = want
		m.dirty = true
	}
}

func substitute(t ast.BaseTerm, s ast.Subst) ast.BaseTerm {
	switch t := t.(type) {
	case ast.Variable:
		if v, ok := s.Get(t).(ast.Constant); ok {
			return v
		}
	case ast.ApplyFn:
		args := make([]ast.BaseTerm, len(t.Args))
		for i, a := range t.Args {
			args[i] = substitute(a, s)
		}
		return ast.ApplyFn{Function: t.Function, Args: args}
	}
	return t
}

func substituteAtom(a ast.Atom, s ast.Subst) ast.Atom {
	args := make([]ast.BaseTerm, len(a.Args))
	for i, t := range a.Args {
		args[i] = substitute(t, s)
	}
	return ast.Atom{Predicate: a.Predicate, Args: args}
}

func substitutePremise(p ast.Term, s ast.Subst) ast.Term {
	switch p := p.(type) {
	case ast.Atom:
		return substituteAtom(p, s)
	case ast.NegAtom:
		return ast.NegAtom{Atom: substituteAtom(p.Atom, s)}
	case ast.Eq:
		return ast.Eq{Left: substitute(p.Left, s), Right: substitute(p.Right, s)}
	case ast.Ineq:
		return ast.Ineq{Left: substitute(p.Left, s), Right: substitute(p.Right, s)}
	}
	return p
}

func (m *machine) giveReasons() {
	want := map[string]ast.Atom{}
	rank := map[string]int{}
	add := func(said, why string) {
		a := fact(reasonVerb, str(said), str(why))
		if _, ok := want[a.String()]; !ok {
			want[a.String()] = a
			rank[a.String()] = len(rank)
		}
	}
	type account struct {
		key  string
		said string
		whys []string
	}
	var accounts []account
	for _, f := range m.firings {
		a := account{said: plainAtom(f.head, false)}
		position := len(m.rules)
		if r := m.ruleOf[f.rule.String()]; r != nil {
			a.whys = append(a.whys, r.id)
			position = r.index
		}
		for _, p := range f.rule.Premises {
			a.whys = append(a.whys, plainPremise(substitutePremise(p, f.subst)))
		}
		a.key = fmt.Sprintf("%s\x00%08d\x00%s", a.said, position, strings.Join(a.whys, "\x00"))
		accounts = append(accounts, a)
	}
	for _, s := range m.stated {
		if m.reasonPreds[s.atom.Predicate] {
			for _, id := range s.ids {
				said := plainAtom(s.atom, false)
				accounts = append(accounts, account{key: said + "\x00" + id, said: said, whys: []string{id}})
			}
		}
	}
	sort.Slice(accounts, func(i, j int) bool { return accounts[i].key < accounts[j].key })
	for _, a := range accounts {
		for _, why := range a.whys {
			add(a.said, why)
		}
	}
	m.reasonRank = rank
	reason := mangleName(reasonVerb)
	same := true
	count := 0
	for key, b := range m.base {
		if b.atom.Predicate.Symbol == reason && b.creator == engineFile {
			count++
			if _, ok := want[key]; !ok {
				same = false
			}
		}
	}
	if same && count == len(want) {
		return
	}
	for key, b := range m.base {
		if b.atom.Predicate.Symbol == reason && b.creator == engineFile {
			delete(m.base, key)
		}
	}
	for _, a := range want {
		m.create(engineFile, a)
	}
	m.dirty = true
}

func (m *machine) printedViews() []string {
	var views []string
	for _, v := range m.about("prints", 2, engineFile) {
		if s, ok := text(v); ok {
			views = append(views, s)
		}
	}
	return m.ordered(views)
}

func (m *machine) executes(file, name string, arity int) bool {
	switch file {
	case engineFile:
		if n, ok := engineInstructions[name]; ok {
			return n == arity
		}
		if arity == 1 && strings.HasPrefix(name, "in ") {
			for _, v := range m.printedViews() {
				if "in "+v == name {
					return true
				}
			}
		}
	case toolsFile:
		if n, ok := toolInstructions[name]; ok {
			return n == arity
		}
	}
	return false
}

func (m *machine) checkInstructions() {
	declared := map[string]map[string]int{engineFile: {}, toolsFile: {}}
	for _, row := range m.rows("executes instruction", 2) {
		file, ok1 := text(row[0])
		pattern, ok2 := text(row[1])
		if !ok1 || !ok2 {
			m.problem(fmt.Sprintf("%s, executes instruction, %s cannot be followed", row[0].String(), row[1].String()))
			continue
		}
		lit, err := patternLiteral(pattern)
		if err != nil {
			m.problem(fmt.Sprintf("%q is not a fact pattern: %v", pattern, err))
			continue
		}
		name := plainName(lit.name)
		if declared[file] == nil {
			m.problem(fmt.Sprintf("%s cannot execute instructions", file))
			continue
		}
		if !m.executes(file, name, len(lit.args)) {
			m.problem(fmt.Sprintf("%s cannot execute %q", file, pattern))
			continue
		}
		declared[file][name] = len(lit.args)
	}
	need := map[string]map[string]int{engineFile: {}, toolsFile: {}}
	for name, n := range engineInstructions {
		need[engineFile][name] = n
	}
	for _, v := range m.printedViews() {
		if wordsForm.MatchString("in " + v) {
			need[engineFile]["in "+v] = 1
		}
	}
	for name, n := range toolInstructions {
		need[toolsFile][name] = n
	}
	for _, file := range []string{engineFile, toolsFile} {
		var missing []string
		for name, n := range need[file] {
			if declared[file][name] != n {
				missing = append(missing, name)
			}
		}
		sort.Strings(missing)
		for _, name := range missing {
			m.problem(fmt.Sprintf("%s executes %q facts, but no line says so", file, name))
		}
	}
}

func (m *machine) checkCreations() {
	allowed := map[string]map[ast.PredicateSym]bool{}
	for _, row := range m.rows("creates fact", 2) {
		file, ok1 := text(row[0])
		pattern, ok2 := text(row[1])
		if !ok1 || !ok2 {
			continue
		}
		lit, err := patternLiteral(pattern)
		if err != nil {
			continue
		}
		if allowed[file] == nil {
			allowed[file] = map[ast.PredicateSym]bool{}
		}
		allowed[file][lit.atom().Predicate] = true
	}
	var found []string
	seen := map[string]bool{}
	for _, b := range m.base {
		if allowed[b.creator][b.atom.Predicate] {
			continue
		}
		msg := fmt.Sprintf("%s creates %q facts, but no line says so", b.creator, plainName(b.atom.Predicate.Symbol))
		if !seen[msg] {
			seen[msg] = true
			found = append(found, msg)
		}
	}
	sort.Strings(found)
	for _, msg := range found {
		m.problem(msg)
	}
}

func (m *machine) checkMeanings() {
	for _, row := range m.rows("means in mangle", 2) {
		plain, ok1 := text(row[0])
		want, ok2 := text(row[1])
		if !ok1 || !ok2 {
			m.problem(fmt.Sprintf("%s, means in mangle, %s is not about text", row[0].String(), row[1].String()))
			continue
		}
		got, err := plainMeaning(plain)
		if err != nil {
			m.problem(fmt.Sprintf("%q cannot be put in mangle: %v", plain, err))
			continue
		}
		if got != want {
			m.problem(fmt.Sprintf("%q means %s in mangle, not %s", plain, got, want))
		}
	}
}

func (m *machine) checkPrinting() {
	for _, row := range m.rows("prints in", 2) {
		file, _ := text(row[0])
		if file != engineFile {
			m.problem(fmt.Sprintf("%s does not print", row[0].String()))
		} else if lang, _ := text(row[1]); lang != plainLanguage {
			m.problem(fmt.Sprintf("%s cannot print in %s", engineFile, row[1].String()))
		}
	}
	for _, row := range m.rows("prints to", 2) {
		file, _ := text(row[0])
		if file != engineFile {
			m.problem(fmt.Sprintf("%s does not print", row[0].String()))
		} else if to, _ := text(row[1]); to != standardOutput {
			m.problem(fmt.Sprintf("%s cannot print to %s", engineFile, row[1].String()))
		}
	}
	for _, row := range m.rows("prints", 2) {
		if file, _ := text(row[0]); file != engineFile {
			m.problem(fmt.Sprintf("%s does not print", row[0].String()))
		}
	}
}

func (m *machine) checkCommands() {
	var gone []string
	for _, c := range m.executed {
		if !m.holds(fact("uses", str(c.name), str(c.tool), str(c.input))) {
			gone = append(gone, fmt.Sprintf("%s used %s on %s, but nothing asks for that any more", c.name, c.tool, c.input))
		}
	}
	sort.Strings(gone)
	for _, g := range gone {
		m.problem(g)
	}
}

func (m *machine) answer() (string, error) {
	answers := map[string]bool{}
	for _, row := range m.rows("conforms", 2) {
		answers[valueText(row[1])] = true
	}
	if len(answers) != 1 {
		return "", fmt.Errorf("the folder should have one answer, and it has %d", len(answers))
	}
	for a := range answers {
		return a, nil
	}
	return "", nil
}

func (m *machine) codeFor(answer string) (int, error) {
	var codes []int64
	for _, c := range m.about("exits with", 2, answer) {
		if c.Type != ast.NumberType {
			return 0, fmt.Errorf("%s exits with %s, which is not a number", answer, c.String())
		}
		codes = append(codes, c.NumValue)
	}
	if len(codes) != 1 {
		return 0, fmt.Errorf("%s should exit with one code, and it has %d", answer, len(codes))
	}
	return int(codes[0]), nil
}

func (m *machine) checkAnswer() {
	if len(m.problems()) > 0 {
		return
	}
	a, err := m.answer()
	if err != nil {
		m.problem(err.Error())
		return
	}
	if _, err := m.codeFor(a); err != nil {
		m.problem(err.Error())
	}
}

func (m *machine) exitCode() int {
	answer := brokenAnswer
	if len(m.problems()) == 0 {
		if a, err := m.answer(); err == nil {
			answer = a
		}
	}
	if code, err := m.codeFor(answer); err == nil {
		return code
	}
	return brokenFallback
}

func (m *machine) factLines(pattern ast.Atom) []string {
	if m.store == nil {
		return nil
	}
	var out []string
	_ = m.store.GetFacts(pattern, func(a ast.Atom) error {
		out = append(out, plainAtom(a, false))
		return nil
	})
	sort.Strings(out)
	return out
}

func (m *machine) printViews(w io.Writer) bool {
	for _, row := range m.rows("prints to", 2) {
		if to, _ := text(row[1]); to != standardOutput {
			return false
		}
	}
	for _, row := range m.rows("prints in", 2) {
		if lang, _ := text(row[1]); lang != plainLanguage {
			return false
		}
	}
	views := m.printedViews()
	var blocks [][]string
	for _, v := range views {
		blocks = append(blocks, m.viewBlocks(v)...)
	}
	for i, b := range blocks {
		if i > 0 {
			fmt.Fprintln(w)
		}
		for _, line := range b {
			fmt.Fprintln(w, line)
		}
	}
	return len(views) > 0
}

func (m *machine) viewBlocks(view string) [][]string {
	var blocks [][]string
	if member := "in " + view; wordsForm.MatchString(member) {
		ids := map[string]bool{}
		for _, row := range m.rows(member, 1) {
			if s, ok := text(row[0]); ok {
				ids[s] = true
			}
		}
		var block []string
		last := ""
		for _, r := range m.rules {
			if !ids[r.id] {
				continue
			}
			if len(block) > 0 && (r.blankBefore || r.file != last) {
				blocks = append(blocks, block)
				block = nil
			}
			block = append(block, plainClause(r.clause)...)
			last = r.file
		}
		if len(block) > 0 {
			blocks = append(blocks, block)
		}
	}
	printed := map[string]bool{}
	patterns := func(words string) []literal {
		var values []string
		for _, c := range m.about(words, 2, view) {
			if s, ok := text(c); ok {
				values = append(values, s)
			}
		}
		values = m.ordered(values)
		stated := func(s string) int {
			if at, ok := m.factAt[fact(words, str(view), str(s)).String()]; ok {
				return at
			}
			return -1
		}
		sort.SliceStable(values, func(i, j int) bool { return stated(values[i]) < stated(values[j]) })
		var out []literal
		for _, s := range values {
			if lit, err := patternLiteral(s); err == nil {
				out = append(out, lit)
			}
		}
		return out
	}
	reasonsOf := map[string][]string{}
	claimed := map[string]bool{}
	var explained []string
	for _, lit := range patterns("gives reasons for") {
		for _, said := range m.factLines(lit.atom()) {
			whys := m.about(reasonVerb, 2, said)
			sort.SliceStable(whys, func(i, j int) bool {
				return m.reasonRank[fact(reasonVerb, str(said), whys[i]).String()] < m.reasonRank[fact(reasonVerb, str(said), whys[j]).String()]
			})
			for _, why := range whys {
				line := plainAtom(fact(reasonVerb, str(said), why), false)
				if !claimed[line] {
					claimed[line] = true
					if len(reasonsOf[said]) == 0 {
						explained = append(explained, said)
					}
					reasonsOf[said] = append(reasonsOf[said], line)
				}
			}
		}
	}
	for _, lit := range patterns("shows") {
		var block, reasons []string
		for _, line := range m.factLines(lit.atom()) {
			if printed[line] || claimed[line] {
				continue
			}
			printed[line] = true
			block = append(block, line)
			for _, why := range reasonsOf[line] {
				if !printed[why] {
					printed[why] = true
					reasons = append(reasons, why)
				}
			}
		}
		if len(block) > 0 {
			blocks = append(blocks, block)
		}
		if len(reasons) > 0 {
			blocks = append(blocks, reasons)
		}
	}
	var rest []string
	for _, said := range explained {
		for _, why := range reasonsOf[said] {
			if !printed[why] {
				printed[why] = true
				rest = append(rest, why)
			}
		}
	}
	if len(rest) > 0 {
		blocks = append(blocks, rest)
	}
	return blocks
}
