package main

import (
	"fmt"
	"io"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/google/mangle/analysis"
	"github.com/google/mangle/ast"
	"github.com/google/mangle/engine"
	"github.com/google/mangle/factstore"
	"github.com/google/mangle/parse"
	"github.com/google/mangle/unionfind"
)

const (
	selfName      = "engine.go"
	firstFile     = "spec.plain"
	knowledgeView = "the knowledge view"
	brokenAnswer  = "broken"
	fallbackCode  = 2
	maxRounds     = 50
	unstated      = int(^uint(0) >> 1)
	joinVerb      = "is the join of"
	differsVerb   = "differs from"
	concatName    = "fn:string:concat"
)

var (
	wordsPattern  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	blankPattern  = regexp.MustCompile(`^\[([^\[\]]*)\]$`)
	numberPattern = regexp.MustCompile(`^-?[0-9]+$`)
	slotPattern   = regexp.MustCompile(`\[([^\[\]]+)\]`)
	builtinVerbs  = map[string]string{
		"ends with":   ":string:ends_with",
		"starts with": ":string:starts_with",
	}
	patternVerbs = map[string]bool{
		"executes instruction": true,
		"creates fact":         true,
		"shows":                true,
		"gives reasons for":    true,
	}
)

type part struct {
	text   string
	quoted bool
}

type rule struct {
	id     string
	file   string
	text   []string
	head   ast.Atom
	body   []ast.Term
	broken bool
	ready  bool
	clause ast.Clause
}

type call struct {
	command ast.Constant
	tool    string
	input   string
}

type problemList struct {
	seen  map[string]bool
	items []string
}

func (p *problemList) add(text string) {
	if p.seen == nil {
		p.seen = map[string]bool{}
	}
	if p.seen[text] {
		return
	}
	p.seen[text] = true
	p.items = append(p.items, text)
}

func (p *problemList) facts() []ast.Atom {
	var out []ast.Atom
	for _, text := range p.items {
		out = append(out, fact("a problem", ast.String(text)))
	}
	return out
}

func main() {
	change := len(os.Args) > 1 && os.Args[1] == "change"
	os.Exit(run(change))
}

func run(change bool) int {
	var problems problemList
	rules := load(&problems)
	var readBack []string
	for _, r := range rules {
		if r.broken {
			continue
		}
		if r.prepare(&problems) {
			readBack = append(readBack, r.id)
		}
	}
	observed := observe(rules, readBack, change)
	order := statedOrder(rules)
	shop := workshop{change: change, order: order}

	executed := map[string]bool{}
	var returned []ast.Atom
	var store factstore.SimpleInMemoryStore
	for round := 0; ; round++ {
		store = evaluate(rules, join(observed, problems.facts(), returned), &problems)
		pending := pendingCalls(store, executed)
		if len(pending) == 0 {
			break
		}
		if round == maxRounds {
			problems.add(fmt.Sprintf("the commands still called new tools after %d rounds", maxRounds))
			break
		}
		shop.store = store
		for _, res := range runCalls(pending, shop) {
			returned = append(returned, res.returned...)
			for _, text := range res.problems {
				problems.add(text)
			}
		}
	}

	reasons := explain(store, rules)
	checkMeanings(store, &problems)
	outputs := printing(store, &problems)
	store = evaluate(rules, join(observed, problems.facts(), returned, reasons), &problems)
	code := decide(store, &problems)
	for _, out := range outputs {
		for _, view := range out.views {
			printView(out.place, view, store, rules, order)
		}
	}
	return code
}

func join(lists ...[]ast.Atom) []ast.Atom {
	var out []ast.Atom
	for _, l := range lists {
		out = append(out, l...)
	}
	return out
}

func load(problems *problemList) []*rule {
	var rules []*rule
	seen := map[string]bool{}
	queue := []string{firstFile}
	for len(queue) > 0 {
		file := queue[0]
		queue = queue[1:]
		if seen[file] {
			continue
		}
		seen[file] = true
		data, err := os.ReadFile(file)
		if err != nil {
			if !os.IsNotExist(err) {
				problems.add(fmt.Sprintf("%s cannot load %s: %v", selfName, file, err))
			}
			continue
		}
		loaded, found := readPlain(file, string(data))
		for _, text := range found {
			problems.add(text)
		}
		for _, r := range loaded {
			rules = append(rules, r)
			if r.broken || len(r.body) > 0 || r.head.Predicate != symbolOf("loads", 2) {
				continue
			}
			who, ok1 := stringOf(r.head.Args[0])
			what, ok2 := stringOf(r.head.Args[1])
			if ok1 && ok2 && who == selfName {
				queue = append(queue, what)
			}
		}
	}
	return rules
}

func readPlain(file, src string) ([]*rule, []string) {
	var rules []*rule
	var problems []string
	var cur *rule
	lines := strings.Split(src, "\n")
	if n := len(lines); n > 0 && lines[n-1] == "" {
		lines = lines[:n-1]
	}
	for i, raw := range lines {
		at := fmt.Sprintf("%s:%d", file, i+1)
		if strings.TrimSpace(raw) == "" {
			continue
		}
		if raw[0] == ' ' || raw[0] == '\t' {
			if cur == nil {
				problems = append(problems, fmt.Sprintf("%s: the condition %s has no rule above it", at, strings.TrimSpace(raw)))
				continue
			}
			cur.text = append(cur.text, raw)
			if cur.broken {
				continue
			}
			t, err := parseCondition(strings.TrimLeft(raw, " \t"))
			if err != nil {
				cur.broken = true
				problems = append(problems, fmt.Sprintf("%s: %v", at, err))
				continue
			}
			cur.body = append(cur.body, t)
			continue
		}
		cur = &rule{id: at, file: file, text: []string{raw}}
		rules = append(rules, cur)
		t, err := parseLine(raw)
		if err != nil {
			cur.broken = true
			problems = append(problems, fmt.Sprintf("%s: %v", at, err))
			continue
		}
		a, ok := t.(ast.Atom)
		if !ok || a.Predicate.IsBuiltin() {
			cur.broken = true
			problems = append(problems, fmt.Sprintf("%s: %s can only be a condition", at, raw))
			continue
		}
		cur.head = a
	}
	return rules, problems
}

func parseCondition(s string) (ast.Term, error) {
	switch {
	case strings.HasPrefix(s, "if "):
		s = s[3:]
	case strings.HasPrefix(s, "and "):
		s = s[4:]
	default:
		return nil, fmt.Errorf("the condition %s starts with neither if nor and", s)
	}
	negated := strings.HasPrefix(s, "not ")
	if negated {
		s = s[4:]
	}
	t, err := parseLine(s)
	if err != nil || !negated {
		return t, err
	}
	a, ok := t.(ast.Atom)
	if !ok || a.Predicate.IsBuiltin() {
		return nil, fmt.Errorf("%s cannot be negated", s)
	}
	return ast.NegAtom{Atom: a}, nil
}

func parseLine(s string) (ast.Term, error) {
	parts, err := splitParts(s)
	if err != nil {
		return nil, err
	}
	if len(parts) == 1 {
		p := parts[0]
		if p.quoted || !wordsPattern.MatchString(p.text) {
			return nil, fmt.Errorf("%s is neither a name in lowercase words nor a line of three or more parts", s)
		}
		return ast.Atom{Predicate: symbolOf(p.text, 0)}, nil
	}
	if len(parts) == 2 {
		return nil, fmt.Errorf("%s has two parts, and a line has one part or three or more", s)
	}
	verb := parts[1]
	if verb.quoted || !wordsPattern.MatchString(verb.text) {
		return nil, fmt.Errorf("the verb %s of %s is not in lowercase words", verb.text, s)
	}
	var args []ast.BaseTerm
	for i, p := range parts {
		if i == 1 {
			continue
		}
		t, err := toTerm(p)
		if err != nil {
			return nil, err
		}
		args = append(args, t)
	}
	if name, ok := builtinVerbs[verb.text]; ok {
		if len(args) != 2 {
			return nil, fmt.Errorf("%s needs exactly one thing on each side of %s", s, verb.text)
		}
		return ast.Atom{Predicate: ast.PredicateSym{Symbol: name, Arity: 2}, Args: args}, nil
	}
	switch {
	case verb.text == differsVerb:
		if len(args) != 2 {
			return nil, fmt.Errorf("%s needs exactly one thing on each side of %s", s, verb.text)
		}
		return ast.Ineq{Left: args[0], Right: args[1]}, nil
	case verb.text == joinVerb:
		rest := args[1:]
		return ast.Eq{Left: args[0], Right: ast.ApplyFn{Function: ast.FunctionSym{Symbol: concatName, Arity: len(rest)}, Args: rest}}, nil
	case verb.text == "is" && len(parts) == 3 && !parts[2].quoted && wordsPattern.MatchString(parts[2].text):
		return ast.Atom{Predicate: symbolOf(parts[2].text, 1), Args: args[:1]}, nil
	}
	return ast.Atom{Predicate: symbolOf(verb.text, len(args)), Args: args}, nil
}

func splitParts(s string) ([]part, error) {
	var parts []part
	i := 0
	for {
		for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i < len(s) && (s[i] == '"' || s[i] == '\'') {
			q := s[i]
			i++
			var b strings.Builder
			closed := false
			for i < len(s) {
				c := s[i]
				if c == '\\' && i+1 < len(s) {
					switch s[i+1] {
					case 'n':
						b.WriteByte('\n')
					case 't':
						b.WriteByte('\t')
					case 'r':
						b.WriteByte('\r')
					default:
						b.WriteByte(s[i+1])
					}
					i += 2
					continue
				}
				i++
				if c == q {
					closed = true
					break
				}
				b.WriteByte(c)
			}
			if !closed {
				return nil, fmt.Errorf("a quote in %s is never closed", s)
			}
			for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
				i++
			}
			if i < len(s) && s[i] != ',' {
				return nil, fmt.Errorf("a closing quote in %s is followed by more text", s)
			}
			parts = append(parts, part{text: b.String(), quoted: true})
		} else {
			j := strings.IndexByte(s[i:], ',')
			end := len(s)
			if j >= 0 {
				end = i + j
			}
			text := strings.TrimSpace(s[i:end])
			if text == "" {
				return nil, fmt.Errorf("%s has an empty part", s)
			}
			parts = append(parts, part{text: text})
			i = end
		}
		if i >= len(s) {
			return parts, nil
		}
		i++
		if strings.TrimSpace(s[i:]) == "" {
			return nil, fmt.Errorf("%s ends with a comma", s)
		}
	}
}

func toTerm(p part) (ast.BaseTerm, error) {
	if p.quoted {
		return ast.String(p.text), nil
	}
	if m := blankPattern.FindStringSubmatch(p.text); m != nil {
		if !wordsPattern.MatchString(m[1]) {
			return nil, fmt.Errorf("the blank %s is not named in lowercase words", p.text)
		}
		return ast.Variable{Symbol: camel(m[1])}, nil
	}
	if numberPattern.MatchString(p.text) {
		n, err := strconv.ParseInt(p.text, 10, 64)
		if err != nil {
			return nil, fmt.Errorf("the number %s is too large", p.text)
		}
		return ast.Number(n), nil
	}
	return ast.String(p.text), nil
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
	for i := 1; i < len(name); i++ {
		if name[i] >= 'A' && name[i] <= 'Z' {
			words = append(words, strings.ToLower(name[start:i]))
			start = i
		}
	}
	words = append(words, strings.ToLower(name[start:]))
	return strings.Join(words, " ")
}

func symbolOf(words string, arity int) ast.PredicateSym {
	return ast.PredicateSym{Symbol: strings.ReplaceAll(words, " ", "_"), Arity: arity}
}

func wordsOf(sym ast.PredicateSym) string {
	return strings.ReplaceAll(sym.Symbol, "_", " ")
}

func fact(words string, args ...ast.BaseTerm) ast.Atom {
	return ast.Atom{Predicate: symbolOf(words, len(args)), Args: args}
}

func stringOf(b ast.BaseTerm) (string, bool) {
	c, ok := b.(ast.Constant)
	if !ok || c.Type != ast.StringType {
		return "", false
	}
	return c.Symbol, true
}

func textOf(b ast.BaseTerm) (string, bool) {
	c, ok := b.(ast.Constant)
	if !ok {
		return "", false
	}
	switch c.Type {
	case ast.StringType:
		return c.Symbol, true
	case ast.NumberType:
		return strconv.FormatInt(c.NumValue, 10), true
	}
	return "", false
}

func mangleBase(b ast.BaseTerm) string {
	switch x := b.(type) {
	case ast.Variable:
		return x.Symbol
	case ast.ApplyFn:
		var args []string
		for _, a := range x.Args {
			args = append(args, mangleBase(a))
		}
		return x.Function.Symbol + "(" + strings.Join(args, ", ") + ")"
	}
	return b.String()
}

func mangleTerm(t ast.Term) string {
	switch x := t.(type) {
	case ast.Atom:
		var args []string
		for _, a := range x.Args {
			args = append(args, mangleBase(a))
		}
		return x.Predicate.Symbol + "(" + strings.Join(args, ", ") + ")"
	case ast.NegAtom:
		return "!" + mangleTerm(x.Atom)
	case ast.Eq:
		return mangleBase(x.Left) + " = " + mangleBase(x.Right)
	case ast.Ineq:
		return mangleBase(x.Left) + " != " + mangleBase(x.Right)
	}
	return t.String()
}

func mangleLine(t ast.Term) string {
	if a, ok := t.(ast.Atom); ok && !a.Predicate.IsBuiltin() {
		return mangleTerm(t) + "."
	}
	return mangleTerm(t)
}

func mangleRule(head ast.Atom, body []ast.Term) string {
	if len(body) == 0 {
		return mangleTerm(head) + "."
	}
	var conditions []string
	for _, t := range body {
		conditions = append(conditions, mangleTerm(t))
	}
	return mangleTerm(head) + " :- " + strings.Join(conditions, ", ") + "."
}

func needsQuotes(s string) bool {
	switch {
	case s == "", strings.TrimSpace(s) != s, strings.ContainsAny(s, ",\n\r\t"):
		return true
	case s[0] == '"' || s[0] == '\'':
		return true
	case blankPattern.MatchString(s), numberPattern.MatchString(s), strings.HasPrefix(s, "not "):
		return true
	}
	return false
}

func quote(s string) string {
	q := '"'
	if strings.ContainsRune(s, '"') && !strings.ContainsRune(s, '\'') {
		q = '\''
	}
	var b strings.Builder
	b.WriteRune(q)
	for _, r := range s {
		switch r {
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		case q:
			b.WriteRune('\\')
			b.WriteRune(r)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteRune(q)
	return b.String()
}

func writeValue(s string) string {
	if needsQuotes(s) {
		return quote(s)
	}
	return s
}

func plainValue(b ast.BaseTerm) (string, error) {
	switch x := b.(type) {
	case ast.Variable:
		return "[" + uncamel(x.Symbol) + "]", nil
	case ast.Constant:
		switch x.Type {
		case ast.StringType:
			return writeValue(x.Symbol), nil
		case ast.NumberType:
			return strconv.FormatInt(x.NumValue, 10), nil
		}
	}
	return "", fmt.Errorf("%v has no plain form", b)
}

func plainValues(args []ast.BaseTerm) ([]string, error) {
	var out []string
	for _, a := range args {
		v, err := plainValue(a)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}

func plainTerm(t ast.Term) (string, error) {
	switch x := t.(type) {
	case ast.NegAtom:
		s, err := plainTerm(x.Atom)
		return "not " + s, err
	case ast.Ineq:
		v, err := plainValues([]ast.BaseTerm{x.Left, x.Right})
		if err != nil {
			return "", err
		}
		return v[0] + ", " + differsVerb + ", " + v[1], nil
	case ast.Eq:
		fn, ok := x.Right.(ast.ApplyFn)
		if !ok || fn.Function.Symbol != concatName {
			return "", fmt.Errorf("%v has no plain form", t)
		}
		v, err := plainValues(append([]ast.BaseTerm{x.Left}, fn.Args...))
		if err != nil {
			return "", err
		}
		return v[0] + ", " + joinVerb + ", " + strings.Join(v[1:], ", "), nil
	case ast.Atom:
		v, err := plainValues(x.Args)
		if err != nil {
			return "", err
		}
		if x.Predicate.IsBuiltin() {
			for verb, name := range builtinVerbs {
				if name == x.Predicate.Symbol && len(v) == 2 {
					return v[0] + ", " + verb + ", " + v[1], nil
				}
			}
			return "", fmt.Errorf("%v has no plain form", t)
		}
		words := wordsOf(x.Predicate)
		if !wordsPattern.MatchString(words) {
			return "", fmt.Errorf("%v has no plain form", t)
		}
		switch len(v) {
		case 0:
			return words, nil
		case 1:
			return v[0] + ", is, " + words, nil
		}
		if words == "is" && len(v) == 2 {
			if s, ok := stringOf(x.Args[1]); ok && wordsPattern.MatchString(s) {
				v[1] = quote(s)
			}
		}
		return v[0] + ", " + words + ", " + strings.Join(v[1:], ", "), nil
	}
	return "", fmt.Errorf("%v has no plain form", t)
}

func plainRule(c ast.Clause) ([]string, error) {
	head, err := plainTerm(c.Head)
	if err != nil {
		return nil, err
	}
	lines := []string{head}
	for i, p := range c.Premises {
		s, err := plainTerm(p)
		if err != nil {
			return nil, err
		}
		keyword := "    and "
		if i == 0 {
			keyword = "    if "
		}
		lines = append(lines, keyword+s)
	}
	return lines, nil
}

func (r *rule) prepare(problems *problemList) bool {
	text := mangleRule(r.head, r.body)
	c, err := parse.Clause(text)
	if err != nil {
		problems.add(fmt.Sprintf("%s means %s in mangle, which mangle cannot read: %v", r.id, text, err))
		return false
	}
	r.clause = c
	r.ready = true
	back, err := plainRule(c)
	return err != nil || strings.Join(back, "\n") != strings.Join(r.text, "\n")
}

func termVariables(t ast.Term, add func(ast.Variable)) {
	var base func(b ast.BaseTerm)
	base = func(b ast.BaseTerm) {
		switch x := b.(type) {
		case ast.Variable:
			add(x)
		case ast.ApplyFn:
			for _, a := range x.Args {
				base(a)
			}
		}
	}
	switch x := t.(type) {
	case ast.Atom:
		for _, a := range x.Args {
			base(a)
		}
	case ast.NegAtom:
		termVariables(x.Atom, add)
	case ast.Eq:
		base(x.Left)
		base(x.Right)
	case ast.Ineq:
		base(x.Left)
		base(x.Right)
	}
}

func patternPredicate(p string) (string, int) {
	slots := slotPattern.FindAllString(p, -1)
	text := strings.Join(strings.Fields(slotPattern.ReplaceAllString(p, " ")), " ")
	if len(slots) == 1 && strings.HasPrefix(p, "[") && strings.HasPrefix(text, "is ") {
		return text[3:], 1
	}
	return text, len(slots)
}

func observe(rules []*rule, readBack []string, change bool) []ast.Atom {
	var out []ast.Atom
	patterns := map[string]bool{}
	for _, r := range rules {
		if !r.ready {
			continue
		}
		head := r.clause.Head
		words := wordsOf(head.Predicate)
		id := ast.String(r.id)
		out = append(out, fact("has a rule for", ast.String(r.file), ast.String(words)))
		out = append(out, fact("defines", id, ast.String(words)))
		blanks := map[string]bool{}
		addBlank := func(v ast.Variable) {
			blanks[uncamel(v.Symbol)] = true
		}
		termVariables(head, addBlank)
		for _, p := range r.clause.Premises {
			termVariables(p, addBlank)
			var a ast.Atom
			switch x := p.(type) {
			case ast.Atom:
				a = x
			case ast.NegAtom:
				a = x.Atom
			default:
				continue
			}
			if !a.Predicate.IsBuiltin() {
				out = append(out, fact("refers to", id, ast.String(wordsOf(a.Predicate))))
			}
		}
		for blank := range blanks {
			out = append(out, fact("has the blank", id, ast.String(blank)))
		}
		if head.Predicate == symbolOf("breaks", 2) {
			if law, ok := stringOf(head.Args[1]); ok {
				out = append(out, fact("lays down", id, ast.String(law)))
			}
		}
		if patternVerbs[words] && head.Predicate.Arity == 2 {
			if p, ok := stringOf(head.Args[1]); ok {
				patterns[p] = true
			}
		}
	}
	for p := range patterns {
		words, _ := patternPredicate(p)
		out = append(out, fact("names", ast.String(p), ast.String(words)))
		for _, m := range slotPattern.FindAllStringSubmatch(p, -1) {
			out = append(out, fact("has the slot", ast.String(p), ast.String(m[1])))
		}
	}
	for _, id := range readBack {
		out = append(out, fact("read back differently", ast.String(id)))
	}
	if change {
		out = append(out, fact("this run is a change"))
	}
	return out
}

func statedOrder(rules []*rule) map[string]int {
	order := map[string]int{}
	for i, r := range rules {
		if !r.ready || len(r.clause.Premises) > 0 {
			continue
		}
		key := r.clause.Head.String()
		if _, ok := order[key]; !ok {
			order[key] = i
		}
	}
	return order
}

func premiseSymbol(t ast.Term) (ast.PredicateSym, bool) {
	switch x := t.(type) {
	case ast.Atom:
		return x.Predicate, !x.Predicate.IsBuiltin()
	case ast.NegAtom:
		return x.Atom.Predicate, !x.Atom.Predicate.IsBuiltin()
	}
	return ast.PredicateSym{}, false
}

func evaluate(rules []*rule, facts []ast.Atom, problems *problemList) factstore.SimpleInMemoryStore {
	var clauses []ast.Clause
	defined := map[ast.PredicateSym]bool{}
	for _, r := range rules {
		if r.ready {
			clauses = append(clauses, r.clause)
			defined[r.clause.Head.Predicate] = true
		}
	}
	for _, f := range facts {
		clauses = append(clauses, ast.Clause{Head: f})
		defined[f.Predicate] = true
	}
	extra := map[ast.PredicateSym]ast.Decl{}
	for _, c := range clauses {
		for _, p := range c.Premises {
			if sym, ok := premiseSymbol(p); ok && !defined[sym] {
				extra[sym] = ast.NewSyntheticDeclFromSym(sym)
			}
		}
	}
	store := factstore.NewSimpleInMemoryStore()
	info, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: clauses}, extra)
	if err == nil {
		err = engine.EvalProgram(info, store)
	}
	if err != nil {
		problems.add(fmt.Sprintf("mangle cannot run the knowledge: %v", err))
		for _, c := range clauses {
			if len(c.Premises) == 0 && ground(c.Head) {
				store.Add(c.Head)
			}
		}
	}
	return store
}

func ground(a ast.Atom) bool {
	for _, arg := range a.Args {
		if _, ok := arg.(ast.Constant); !ok {
			return false
		}
	}
	return true
}

func factsOf(store factstore.ReadOnlyFactStore, words string, arity int) []ast.Atom {
	var out []ast.Atom
	store.GetFacts(ast.NewQuery(symbolOf(words, arity)), func(a ast.Atom) error {
		out = append(out, a)
		return nil
	})
	sort.Slice(out, func(i, j int) bool { return out[i].String() < out[j].String() })
	return out
}

func textsOf(store factstore.ReadOnlyFactStore, words, subject string) []string {
	var out []string
	for _, f := range factsOf(store, words, 2) {
		who, ok1 := textOf(f.Args[0])
		what, ok2 := textOf(f.Args[1])
		if ok1 && ok2 && who == subject {
			out = append(out, what)
		}
	}
	return out
}

func pendingCalls(store factstore.ReadOnlyFactStore, executed map[string]bool) []call {
	var out []call
	for _, f := range factsOf(store, "calls", 3) {
		key := f.String()
		if executed[key] {
			continue
		}
		executed[key] = true
		command, ok := f.Args[0].(ast.Constant)
		tool, ok1 := textOf(f.Args[1])
		input, ok2 := textOf(f.Args[2])
		if ok && ok1 && ok2 {
			out = append(out, call{command: command, tool: tool, input: input})
		}
	}
	return out
}

func runCalls(calls []call, shop workshop) []result {
	results := make([]result, len(calls))
	slots := make(chan struct{}, max(2, runtime.NumCPU()))
	var wg sync.WaitGroup
	for i, c := range calls {
		wg.Add(1)
		go func() {
			defer wg.Done()
			slots <- struct{}{}
			results[i] = shop.use(c)
			<-slots
		}()
	}
	wg.Wait()
	return results
}

func evaluationOrder(premises []ast.Term) []ast.Term {
	var first, rest []ast.Term
	for _, p := range premises {
		if a, ok := p.(ast.Atom); ok && !a.Predicate.IsBuiltin() {
			first = append(first, p)
		} else {
			rest = append(rest, p)
		}
	}
	return append(first, rest...)
}

func explain(store factstore.SimpleInMemoryStore, rules []*rule) []ast.Atom {
	var out []ast.Atom
	seen := map[string]bool{}
	query := engine.QueryContext{Store: store}
	for _, g := range factsOf(store, "gives reasons for", 2) {
		p, ok := stringOf(g.Args[1])
		if !ok {
			continue
		}
		words, arity := patternPredicate(p)
		sym := symbolOf(words, arity)
		for _, f := range factsOf(store, words, arity) {
			stated, err := plainTerm(f)
			if err != nil {
				continue
			}
			for _, r := range rules {
				if !r.ready || len(r.clause.Premises) == 0 || r.clause.Head.Predicate != sym {
					continue
				}
				subst, err := unionfind.UnifyTermsExtend(r.clause.Head.Args, f.Args, unionfind.New())
				if err != nil {
					continue
				}
				solutions := []unionfind.UnionFind{subst}
				for _, premise := range evaluationOrder(r.clause.Premises) {
					var next []unionfind.UnionFind
					for _, s := range solutions {
						found, err := query.EvalPremise(premise, s)
						if err == nil {
							next = append(next, found...)
						}
					}
					solutions = next
				}
				for _, s := range solutions {
					for _, premise := range r.clause.Premises {
						reason, err := plainTerm(premise.ApplySubst(s))
						if err != nil {
							continue
						}
						key := stated + "\x00" + reason
						if seen[key] {
							continue
						}
						seen[key] = true
						out = append(out, fact("holds because", ast.String(stated), ast.String(reason)))
					}
				}
			}
		}
	}
	return out
}

func checkMeanings(store factstore.ReadOnlyFactStore, problems *problemList) {
	for _, f := range factsOf(store, "means in mangle", 2) {
		line, ok1 := stringOf(f.Args[0])
		want, ok2 := stringOf(f.Args[1])
		if !ok1 || !ok2 {
			problems.add(fmt.Sprintf("%s does not pair a line with mangle text", f.String()))
			continue
		}
		t, err := parseLine(line)
		if err != nil {
			problems.add(fmt.Sprintf("%s cannot mean %s in mangle: %v", quote(line), want, err))
			continue
		}
		if got := mangleLine(t); got != want {
			problems.add(fmt.Sprintf("%s means %s in mangle, not %s", quote(line), got, want))
		}
	}
}

type output struct {
	place io.Writer
	views []string
}

func printing(store factstore.ReadOnlyFactStore, problems *problemList) []output {
	views := textsOf(store, "prints", selfName)
	if len(views) == 0 {
		return nil
	}
	languages := textsOf(store, "prints in", selfName)
	if len(languages) == 0 {
		problems.add(fmt.Sprintf("%s is not told what language to print in", selfName))
	}
	for _, l := range languages {
		if l != "plain language" {
			problems.add(fmt.Sprintf("%s cannot print in %s", selfName, l))
		}
	}
	places := textsOf(store, "prints to", selfName)
	if len(places) == 0 {
		problems.add(fmt.Sprintf("%s is not told where to print", selfName))
	}
	var out []output
	for _, p := range places {
		switch p {
		case "standard output":
			out = append(out, output{place: os.Stdout, views: views})
		case "standard error":
			out = append(out, output{place: os.Stderr, views: views})
		default:
			problems.add(fmt.Sprintf("%s cannot print to %s", selfName, p))
		}
	}
	return out
}

func decide(store factstore.SimpleInMemoryStore, problems *problemList) int {
	addProblem := func(text string) {
		problems.add(text)
		store.Add(fact("a problem", ast.String(text)))
	}
	answer := brokenAnswer
	if len(factsOf(store, "a problem", 1)) == 0 {
		answers := map[string]bool{}
		for _, f := range factsOf(store, "conforms", 2) {
			if a, ok := textOf(f.Args[1]); ok {
				answers[a] = true
			}
		}
		if len(answers) == 1 {
			for a := range answers {
				answer = a
			}
		} else {
			addProblem(fmt.Sprintf("the knowledge gives %d answers to whether the folder conforms, not one", len(answers)))
		}
	}
	var codes []int64
	for _, f := range factsOf(store, "exits with", 2) {
		a, ok := textOf(f.Args[0])
		c, isConst := f.Args[1].(ast.Constant)
		if ok && a == answer && isConst && c.Type == ast.NumberType {
			codes = append(codes, c.NumValue)
		}
	}
	if len(codes) == 1 {
		return int(codes[0])
	}
	addProblem(fmt.Sprintf("the knowledge gives %d exit codes for %s, not one", len(codes), answer))
	return fallbackCode
}

func printView(w io.Writer, view string, store factstore.ReadOnlyFactStore, rules []*rule, order map[string]int) {
	var lines []string
	if view == knowledgeView {
		inView := map[string]bool{}
		for _, f := range factsOf(store, "in the knowledge view", 1) {
			if id, ok := stringOf(f.Args[0]); ok {
				inView[id] = true
			}
		}
		for _, r := range rules {
			if !r.ready || !inView[r.id] {
				continue
			}
			text, err := plainRule(r.clause)
			if err != nil {
				text = r.text
			}
			if len(text) > 1 && len(lines) > 0 && lines[len(lines)-1] != "" {
				lines = append(lines, "")
			}
			lines = append(lines, text...)
			if len(text) > 1 {
				lines = append(lines, "")
			}
		}
		if len(lines) > 0 && lines[len(lines)-1] != "" {
			lines = append(lines, "")
		}
	}
	type shown struct {
		pattern string
		rank    int
	}
	var patterns []shown
	for _, f := range factsOf(store, "shows", 2) {
		v, ok1 := stringOf(f.Args[0])
		p, ok2 := stringOf(f.Args[1])
		if !ok1 || !ok2 || v != view {
			continue
		}
		rank, ok := order[f.String()]
		if !ok {
			rank = unstated
		}
		patterns = append(patterns, shown{p, rank})
	}
	sort.Slice(patterns, func(i, j int) bool {
		if patterns[i].rank != patterns[j].rank {
			return patterns[i].rank < patterns[j].rank
		}
		return patterns[i].pattern < patterns[j].pattern
	})
	printed := map[string]bool{}
	for _, p := range patterns {
		words, arity := patternPredicate(p.pattern)
		var found []string
		for _, f := range factsOf(store, words, arity) {
			text, err := plainTerm(f)
			if err == nil && !printed[text] {
				printed[text] = true
				found = append(found, text)
			}
		}
		sort.Strings(found)
		lines = append(lines, found...)
	}
	for len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	if len(lines) > 0 {
		fmt.Fprintln(w, strings.Join(lines, "\n"))
	}
}
