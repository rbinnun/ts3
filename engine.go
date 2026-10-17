package main

import (
	"fmt"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	self           = "engine.go"
	kindOfRun      = "KIND_OF_RUN"
	declaredPrefix = "declared: "
	plainLanguage  = "plain language"
	standardError  = "standard error"
	broken         = "broken"
	troubleCode    = 2
	settleLimit    = 64
)

var (
	variableShape = regexp.MustCompile(`^\[[a-z]+( [a-z]+)*\]$`)
	numberShape   = regexp.MustCompile(`^-?[0-9]+$`)
	wordsShape    = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	mangleEscapes = strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`, "\t", `\t`)
	tests         = map[string]string{"starts with": ":string:starts_with", "ends with": ":string:ends_with"}
	testWords     = map[string]string{":string:starts_with": "starts with", ":string:ends_with": "ends with"}
	readings      sync.Map
)

const (
	relationShape = iota
	testShape
	joinShape
	differShape
)

type field struct {
	text   string
	quoted bool
}

type term struct {
	text     string
	number   int64
	variable bool
	numeric  bool
}

type premise struct {
	shape   int
	name    string
	args    []term
	negated bool
}

type rule struct {
	id       string
	declared bool
	head     premise
	body     []premise
	clause   ast.Clause
	text     string
}

type reading struct {
	rules    []*rule
	problems []string
	misread  []string
}

type command struct {
	name, tool, input string
}

type run struct {
	kind     string
	rules    []*rule
	decls    []*rule
	problems []string
	misread  []string
	info     *analysis.ProgramInfo
	helpers  map[string]string
	order    map[string]int
	model    factstore.SimpleInMemoryStore
	fired    map[string]bool
	results  map[string][]ast.Atom
}

func main() {
	r := &run{kind: os.Getenv(kindOfRun), results: map[string][]ast.Atom{}, model: factstore.NewSimpleInMemoryStore()}
	if len(os.Args) < 2 {
		r.problem("no spec was named")
	} else {
		r.load(os.Args[1])
		r.check()
		r.build()
		r.evaluate()
	}
	r.print()
	os.Exit(r.exitCode())
}

func (r *run) problem(text string) {
	text = strings.Join(strings.Fields(text), " ")
	for _, p := range r.problems {
		if p == text {
			return
		}
	}
	r.problems = append(r.problems, text)
}

func (r *run) load(start string) {
	queue := []string{start}
	seen := map[string]bool{}
	for len(queue) > 0 {
		file := queue[0]
		queue = queue[1:]
		if seen[file] {
			continue
		}
		seen[file] = true
		data, err := os.ReadFile(file)
		if err != nil {
			if file == start {
				r.problem(file + " cannot be read")
			}
			continue
		}
		read := readPlain(file, string(data))
		for _, p := range read.problems {
			r.problem(p)
		}
		r.misread = append(r.misread, read.misread...)
		for _, rl := range read.rules {
			if rl.declared {
				r.decls = append(r.decls, rl)
				continue
			}
			r.rules = append(r.rules, rl)
			if target, ok := loadTarget(rl); ok {
				queue = append(queue, target)
			}
		}
	}
}

func loadTarget(rl *rule) (string, bool) {
	h := rl.head
	if len(rl.body) > 0 || h.name != nameOf("loads") || len(h.args) != 2 {
		return "", false
	}
	if !h.args[0].isText() || h.args[0].text != self || !h.args[1].isText() {
		return "", false
	}
	return h.args[1].text, true
}

func (r *run) check() {
	for _, rl := range r.rules {
		h := rl.head
		if len(rl.body) > 0 || h.name != nameOf("means in mangle") || len(h.args) != 2 {
			continue
		}
		if !h.args[0].isText() || !h.args[1].isText() {
			continue
		}
		if got, err := translate(h.args[0].text); err != nil || got != h.args[1].text {
			r.problem("the engine reads " + rl.id + " otherwise")
		}
	}
}

func (r *run) build() {
	var b strings.Builder
	for _, d := range r.decls {
		b.WriteString(d.text + "\n")
	}
	r.helpers = map[string]string{}
	r.order = map[string]int{}
	for i, rl := range r.rules {
		b.WriteString(rl.text + "\n")
		if len(rl.body) == 0 {
			r.order[rl.clause.Head.String()] = i
			continue
		}
		helper := fmt.Sprintf("fired__%d", i)
		r.helpers[helper] = rl.id
		fmt.Fprintf(&b, "%s() :- %s.\n", helper, rl.conditions())
	}
	unit, err := parse.Unit(strings.NewReader(b.String()))
	if err != nil {
		r.problem("the rules cannot be read together: " + err.Error())
		return
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		r.problem("the rules do not hold together: " + err.Error())
		return
	}
	r.info = info
}

func (r *run) evaluate() {
	if r.info == nil {
		r.model = r.factsOnly()
		return
	}
	done := map[string]bool{}
	var live []ast.Atom
	for round := 0; round < settleLimit; round++ {
		model, err := r.evalOnce(live)
		r.model = model
		if err != nil {
			r.problem("the rules cannot be evaluated: " + err.Error())
			return
		}
		r.fired = r.firedRules()
		var fresh []command
		var nextLive []ast.Atom
		for _, c := range r.commands() {
			t, known := toolbox[c.tool]
			switch {
			case known && t.live:
				nextLive = append(nextLive, r.execute(c)...)
			case !done[c.key()]:
				done[c.key()] = true
				fresh = append(fresh, c)
			}
		}
		if len(fresh) == 0 && sameFacts(live, nextLive) {
			return
		}
		r.executeAll(fresh)
		live = nextLive
	}
	r.problem("the run does not settle")
}

func (r *run) engineFacts() []ast.Atom {
	var facts []ast.Atom
	if r.kind != "" {
		facts = append(facts, property(r.kind, "the kind of this run"))
	}
	for _, p := range r.problems {
		facts = append(facts, property(p, "a problem"))
	}
	for _, m := range r.misread {
		facts = append(facts, property(m, "misread"))
	}
	return facts
}

func (r *run) evalOnce(live []ast.Atom) (factstore.SimpleInMemoryStore, error) {
	store := factstore.NewSimpleInMemoryStore()
	for _, f := range r.engineFacts() {
		store.Add(f)
	}
	for _, facts := range r.results {
		for _, f := range facts {
			store.Add(f)
		}
	}
	for _, f := range live {
		store.Add(f)
	}
	return store, engine.EvalProgram(r.info, store)
}

func (r *run) factsOnly() factstore.SimpleInMemoryStore {
	store := factstore.NewSimpleInMemoryStore()
	for _, f := range r.engineFacts() {
		store.Add(f)
	}
	for _, rl := range r.rules {
		if len(rl.body) == 0 {
			store.Add(rl.clause.Head)
		}
	}
	return store
}

func (r *run) firedRules() map[string]bool {
	fired := map[string]bool{}
	for _, rl := range r.rules {
		if len(rl.body) == 0 {
			fired[rl.id] = true
		}
	}
	for helper, id := range r.helpers {
		r.model.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: helper}), func(ast.Atom) error {
			fired[id] = true
			return nil
		})
	}
	return fired
}

func (r *run) commands() []command {
	var cs []command
	r.model.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: nameOf("uses"), Arity: 3}), func(a ast.Atom) error {
		cs = append(cs, command{textOf(a.Args[0]), textOf(a.Args[1]), textOf(a.Args[2])})
		return nil
	})
	sort.Slice(cs, func(i, j int) bool { return cs[i].key() < cs[j].key() })
	return cs
}

func (c command) key() string {
	return c.name + "\x00" + c.tool + "\x00" + c.input
}

func (r *run) execute(c command) []ast.Atom {
	t, ok := toolbox[c.tool]
	if !ok {
		return nil
	}
	var facts []ast.Atom
	for _, f := range t.run(r, c.tool, c.input) {
		facts = append(facts, relation("returned", ast.String(c.name), ast.String(f.field), f.value))
	}
	return facts
}

func (r *run) executeAll(cs []command) {
	found := make([][]ast.Atom, len(cs))
	slots := make(chan struct{}, max(2, runtime.NumCPU()))
	var wg sync.WaitGroup
	for i, c := range cs {
		wg.Add(1)
		go func() {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			found[i] = r.execute(c)
		}()
	}
	wg.Wait()
	for i, c := range cs {
		r.results[c.key()] = found[i]
	}
}

func sameFacts(a, b []ast.Atom) bool {
	seen := map[string]bool{}
	for _, f := range a {
		seen[f.String()] = true
	}
	other := map[string]bool{}
	for _, f := range b {
		if !seen[f.String()] {
			return false
		}
		other[f.String()] = true
	}
	return len(seen) == len(other)
}

func (r *run) facts(words string, args ...ast.BaseTerm) []ast.Atom {
	var found []ast.Atom
	r.model.GetFacts(ast.Atom{Predicate: ast.PredicateSym{Symbol: nameOf(words), Arity: len(args)}, Args: args}, func(a ast.Atom) error {
		found = append(found, a)
		return nil
	})
	sort.SliceStable(found, func(i, j int) bool {
		oi, iok := r.order[found[i].String()]
		oj, jok := r.order[found[j].String()]
		if iok != jok {
			return iok
		}
		if iok && oi != oj {
			return oi < oj
		}
		return found[i].String() < found[j].String()
	})
	return found
}

func (r *run) lookup(words, subject string) (string, bool) {
	for _, a := range r.facts(words, ast.String(subject), ast.Variable{Symbol: "X"}) {
		return textOf(a.Args[1]), true
	}
	return "", false
}

func (r *run) print() {
	out := os.Stdout
	if place, ok := r.lookup("prints to", self); ok && place == standardError {
		out = os.Stderr
	}
	if language, ok := r.lookup("prints in", self); ok && language != plainLanguage {
		r.problem(self + " cannot print in " + language)
	}
	for _, p := range r.problems {
		r.model.Add(property(p, "a problem"))
	}
	if r.answer() == broken {
		for _, f := range r.facts("conforms", ast.Variable{Symbol: "X"}, ast.Variable{Symbol: "Y"}) {
			r.model.Remove(f)
			r.model.Add(relation("conforms", f.Args[0], ast.String(broken)))
		}
	}
	patterns := r.facts("prints", ast.String(self), ast.Variable{Symbol: "X"})
	if len(patterns) == 0 {
		for _, p := range r.problems {
			fmt.Fprintln(out, plainOfAtom(property(p, "a problem")))
		}
		return
	}
	first := true
	for _, a := range patterns {
		line, ok := patternLine(textOf(a.Args[1]))
		if !ok {
			continue
		}
		p, err := readPremise(line)
		if err != nil || p.shape != relationShape {
			continue
		}
		var lines []string
		r.model.GetFacts(p.query(), func(fact ast.Atom) error {
			lines = append(lines, plainOfAtom(fact))
			return nil
		})
		if len(lines) == 0 {
			continue
		}
		sort.Slice(lines, func(i, j int) bool { return naturalLess(lines[i], lines[j]) })
		if !first {
			fmt.Fprintln(out)
		}
		first = false
		fmt.Fprintln(out, strings.Join(lines, "\n"))
	}
}

func (r *run) answer() string {
	if len(r.problems) > 0 {
		return broken
	}
	answers := map[string]bool{}
	for _, a := range r.facts("conforms", ast.Variable{Symbol: "X"}, ast.Variable{Symbol: "Y"}) {
		answers[textOf(a.Args[1])] = true
	}
	if len(answers) != 1 {
		return broken
	}
	for a := range answers {
		return a
	}
	return broken
}

func (r *run) exitCode() int {
	for _, a := range []string{r.answer(), broken} {
		for _, f := range r.facts("exits with", ast.String(a), ast.Variable{Symbol: "X"}) {
			if c, ok := f.Args[1].(ast.Constant); ok && c.Type == ast.NumberType {
				return int(c.NumValue)
			}
		}
	}
	return troubleCode
}

func naturalLess(a, b string) bool {
	for a != "" && b != "" {
		da, db := digitsAt(a), digitsAt(b)
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

func digitsAt(s string) int {
	n := 0
	for n < len(s) && s[n] >= '0' && s[n] <= '9' {
		n++
	}
	return n
}

func property(subject, words string) ast.Atom {
	return ast.NewAtom(nameOf(words), ast.String(subject))
}

func relation(words string, args ...ast.BaseTerm) ast.Atom {
	return ast.NewAtom(nameOf(words), args...)
}

func textOf(t ast.BaseTerm) string {
	if c, ok := t.(ast.Constant); ok {
		switch c.Type {
		case ast.StringType:
			return c.Symbol
		case ast.NumberType:
			return strconv.FormatInt(c.NumValue, 10)
		}
	}
	return t.String()
}

func nameOf(words string) string {
	return strings.ReplaceAll(words, " ", "_")
}

func wordOf(name string) string {
	return strings.ReplaceAll(name, "_", " ")
}

func place(file string, line int) string {
	return file + ":" + strconv.Itoa(line)
}

func readPlain(file, data string) *reading {
	key := file + "\x00" + data
	if known, ok := readings.Load(key); ok {
		return known.(*reading)
	}
	read := &reading{}
	lines := strings.Split(data, "\n")
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var group []int
	flush := func() {
		if len(group) > 0 {
			read.add(file, lines, group)
			group = nil
		}
	}
	for i, l := range lines {
		switch {
		case strings.TrimSpace(l) == "":
			flush()
			if l != "" {
				read.misread = append(read.misread, place(file, i+1))
			}
		case l[0] == ' ' || l[0] == '\t':
			if len(group) == 0 {
				read.problems = append(read.problems, place(file, i+1)+" is a condition without a rule")
				continue
			}
			group = append(group, i)
		default:
			flush()
			group = []int{i}
		}
	}
	flush()
	readings.Store(key, read)
	return read
}

func (read *reading) add(file string, lines []string, group []int) {
	rl := &rule{id: place(file, group[0]+1)}
	headLine := lines[group[0]]
	if rest, ok := strings.CutPrefix(headLine, declaredPrefix); ok {
		rl.declared = true
		headLine = rest
	}
	head, err := readPremise(headLine)
	if err == nil && head.shape != relationShape {
		err = fmt.Errorf("it is a test, not a sentence")
	}
	if err == nil && rl.declared && len(group) > 1 {
		err = fmt.Errorf("a declaration has no conditions")
	}
	if err != nil {
		read.problems = append(read.problems, rl.id+" cannot be read: "+err.Error())
		return
	}
	rl.head = head
	for _, i := range group[1:] {
		p, err := readCondition(lines[i])
		if err != nil {
			read.problems = append(read.problems, place(file, i+1)+" cannot be read: "+err.Error())
			return
		}
		rl.body = append(rl.body, p)
	}
	rl.text = rl.mangle()
	written, err := rl.readBack()
	if err != nil {
		read.problems = append(read.problems, rl.id+" is not mangle: "+err.Error())
		return
	}
	for k, i := range group {
		if k >= len(written) || written[k] != lines[i] {
			read.misread = append(read.misread, place(file, i+1))
		}
	}
	read.rules = append(read.rules, rl)
}

func (rl *rule) readBack() ([]string, error) {
	if rl.declared {
		unit, err := parse.Unit(strings.NewReader(rl.text))
		if err != nil {
			return nil, err
		}
		if len(unit.Decls) == 0 {
			return nil, fmt.Errorf("no declaration in %s", rl.text)
		}
		return []string{declaredPrefix + plainOfAtom(unit.Decls[len(unit.Decls)-1].DeclaredAtom)}, nil
	}
	clause, err := parse.Clause(rl.text)
	if err != nil {
		return nil, err
	}
	rl.clause = clause
	written := []string{plainOfAtom(clause.Head)}
	for i, p := range clause.Premises {
		text, err := plainOfTerm(p)
		if err != nil {
			return nil, err
		}
		keyword := "and "
		if i == 0 {
			keyword = "if "
		}
		written = append(written, "    "+keyword+text)
	}
	return written, nil
}

func (rl *rule) mangle() string {
	if rl.declared {
		return "Decl " + rl.head.mangle() + "."
	}
	if len(rl.body) == 0 {
		return rl.head.mangle() + "."
	}
	return rl.head.mangle() + " :- " + rl.conditions() + "."
}

func (rl *rule) conditions() string {
	var conds []string
	for _, p := range rl.body {
		conds = append(conds, p.mangle())
	}
	return strings.Join(conds, ", ")
}

func readCondition(line string) (premise, error) {
	text := strings.TrimLeft(line, " \t")
	rest, ok := strings.CutPrefix(text, "if ")
	if !ok {
		if rest, ok = strings.CutPrefix(text, "and "); !ok {
			return premise{}, fmt.Errorf("a condition starts with if or and")
		}
	}
	negated := false
	if after, ok := strings.CutPrefix(rest, "not "); ok {
		rest, negated = after, true
	}
	p, err := readPremise(rest)
	p.negated = negated
	return p, err
}

func translate(line string) (string, error) {
	if rest, ok := strings.CutPrefix(line, declaredPrefix); ok {
		p, err := readPremise(rest)
		if err != nil {
			return "", err
		}
		if p.shape != relationShape {
			return "", fmt.Errorf("only sentences are declared")
		}
		return "Decl " + p.mangle() + ".", nil
	}
	p, err := readPremise(line)
	if err != nil {
		return "", err
	}
	if p.shape == relationShape {
		return p.mangle() + ".", nil
	}
	return p.mangle(), nil
}

func splitFields(line string) ([]field, error) {
	var fields []field
	rest := line
	for {
		if rest == "" {
			return nil, fmt.Errorf("a part is empty")
		}
		var f field
		if q := rest[0]; q == '"' || q == '\'' {
			end := -1
			for i := 1; i < len(rest); i++ {
				if rest[i] == q && (i == len(rest)-1 || strings.HasPrefix(rest[i+1:], ", ")) {
					end = i
					break
				}
			}
			if end < 0 {
				return nil, fmt.Errorf("a quote is not closed")
			}
			f, rest = field{rest[1:end], true}, rest[end+1:]
		} else {
			end := strings.Index(rest, ", ")
			if end < 0 {
				end = len(rest)
			}
			f, rest = field{rest[:end], false}, rest[end:]
		}
		fields = append(fields, f)
		if rest == "" {
			return fields, nil
		}
		rest = strings.TrimPrefix(rest, ", ")
	}
}

func readPremise(line string) (premise, error) {
	fields, err := splitFields(line)
	if err != nil {
		return premise{}, err
	}
	switch len(fields) {
	case 1:
		if fields[0].quoted || !wordsShape.MatchString(fields[0].text) {
			return premise{}, fmt.Errorf("a sentence without commas is lower-case words")
		}
		return premise{name: nameOf(fields[0].text)}, nil
	case 2:
		return premise{}, fmt.Errorf("a sentence has a subject, a verb and an object")
	}
	verb, object := fields[1], fields[2]
	if verb.quoted || !wordsShape.MatchString(verb.text) {
		return premise{}, fmt.Errorf("a verb is lower-case words")
	}
	args := []term{termOf(fields[0])}
	for _, f := range fields[2:] {
		args = append(args, termOf(f))
	}
	switch {
	case verb.text == "is" && len(fields) == 3 && !object.quoted && wordsShape.MatchString(object.text):
		return premise{name: nameOf(object.text), args: args[:1]}, nil
	case tests[verb.text] != "" && len(args) == 2:
		return premise{shape: testShape, name: tests[verb.text], args: args}, nil
	case verb.text == "differs from" && len(args) == 2:
		return premise{shape: differShape, args: args}, nil
	case verb.text == "is the join of":
		return premise{shape: joinShape, args: args}, nil
	}
	return premise{name: nameOf(verb.text), args: args}, nil
}

func termOf(f field) term {
	if !f.quoted && variableShape.MatchString(f.text) {
		return term{text: camel(f.text), variable: true}
	}
	if !f.quoted && numberShape.MatchString(f.text) {
		if n, err := strconv.ParseInt(f.text, 10, 64); err == nil {
			return term{number: n, numeric: true}
		}
	}
	return term{text: f.text}
}

func (t term) isText() bool {
	return !t.variable && !t.numeric
}

func (t term) mangle() string {
	switch {
	case t.variable:
		return t.text
	case t.numeric:
		return strconv.FormatInt(t.number, 10)
	}
	return `"` + mangleEscapes.Replace(t.text) + `"`
}

func (t term) base() ast.BaseTerm {
	switch {
	case t.variable:
		return ast.Variable{Symbol: t.text}
	case t.numeric:
		return ast.Number(t.number)
	}
	return ast.String(t.text)
}

func (p premise) mangle() string {
	var args []string
	for _, a := range p.args {
		args = append(args, a.mangle())
	}
	text := p.name + "(" + strings.Join(args, ", ") + ")"
	switch p.shape {
	case joinShape:
		text = args[0] + " = fn:string:concat(" + strings.Join(args[1:], ", ") + ")"
	case differShape:
		text = args[0] + " != " + args[1]
	}
	if p.negated {
		return "!" + text
	}
	return text
}

func (p premise) query() ast.Atom {
	var args []ast.BaseTerm
	for _, a := range p.args {
		args = append(args, a.base())
	}
	return ast.Atom{Predicate: ast.PredicateSym{Symbol: p.name, Arity: len(args)}, Args: args}
}

func camel(v string) string {
	var b strings.Builder
	for _, w := range strings.Fields(strings.Trim(v, "[]")) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	return b.String()
}

func uncamel(v string) string {
	var words []string
	start := 0
	for i := 1; i <= len(v); i++ {
		if i == len(v) || (v[i] >= 'A' && v[i] <= 'Z') {
			words = append(words, strings.ToLower(v[start:i]))
			start = i
		}
	}
	return "[" + strings.Join(words, " ") + "]"
}

func plainOfTerm(t ast.Term) (string, error) {
	switch v := t.(type) {
	case ast.Atom:
		return plainOfAtom(v), nil
	case ast.NegAtom:
		return "not " + plainOfAtom(v.Atom), nil
	case ast.Ineq:
		return plainOfBase(v.Left) + ", differs from, " + plainOfBase(v.Right), nil
	case ast.Eq:
		if fn, ok := v.Right.(ast.ApplyFn); ok && fn.Function.Symbol == "fn:string:concat" {
			parts := []string{plainOfBase(v.Left), "is the join of"}
			for _, a := range fn.Args {
				parts = append(parts, plainOfBase(a))
			}
			return strings.Join(parts, ", "), nil
		}
	}
	return "", fmt.Errorf("%v has no plain reading", t)
}

func plainOfAtom(a ast.Atom) string {
	args := make([]string, len(a.Args))
	for i, arg := range a.Args {
		args[i] = plainOfBase(arg)
	}
	verb, test := testWords[a.Predicate.Symbol]
	if !test {
		verb = wordOf(a.Predicate.Symbol)
	}
	switch {
	case len(args) == 0:
		return verb
	case len(args) == 1 && !test:
		return args[0] + ", is, " + verb
	case verb == "is" && len(args) == 2:
		if c, ok := a.Args[1].(ast.Constant); ok && c.Type == ast.StringType && wordsShape.MatchString(c.Symbol) {
			args[1] = quoted(c.Symbol)
		}
	}
	return strings.Join(append([]string{args[0], verb}, args[1:]...), ", ")
}

func plainOfBase(t ast.BaseTerm) string {
	switch v := t.(type) {
	case ast.Variable:
		return uncamel(v.Symbol)
	case ast.Constant:
		switch v.Type {
		case ast.StringType:
			return plainValue(v.Symbol)
		case ast.NumberType:
			return strconv.FormatInt(v.NumValue, 10)
		}
	}
	return plainValue(t.String())
}

func plainValue(s string) string {
	if s == "" || strings.Contains(s, ", ") || strings.HasPrefix(s, `"`) || strings.HasPrefix(s, "'") ||
		strings.TrimSpace(s) != s || variableShape.MatchString(s) || numberShape.MatchString(s) {
		return quoted(s)
	}
	return s
}

func quoted(s string) string {
	if !strings.Contains(s, `"`) {
		return `"` + s + `"`
	}
	if !strings.Contains(s, `', `) {
		return `'` + s + `'`
	}
	return `"` + s + `"`
}

func patternLine(pattern string) (string, bool) {
	var parts []string
	rest := strings.TrimSpace(pattern)
	for rest != "" {
		end := strings.Index(rest, "[")
		if end == 0 {
			end = strings.Index(rest, "]") + 1
			if end == 0 {
				return "", false
			}
		} else if end < 0 {
			end = len(rest)
		}
		parts = append(parts, strings.TrimSpace(rest[:end]))
		rest = strings.TrimSpace(rest[end:])
	}
	hole := func(s string) bool { return strings.HasPrefix(s, "[") }
	switch {
	case len(parts) == 1 && !hole(parts[0]):
		return parts[0], true
	case len(parts) == 2 && hole(parts[0]) && strings.HasPrefix(parts[1], "is "):
		return parts[0] + ", is, " + strings.TrimPrefix(parts[1], "is "), true
	case len(parts) >= 3 && hole(parts[0]) && !hole(parts[1]):
		for _, p := range parts[2:] {
			if !hole(p) {
				return "", false
			}
		}
		return strings.Join(parts, ", "), true
	}
	return "", false
}
