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
	"codeberg.org/TauCeti/mangle-go/unionfind"
)

const (
	self          = "engine.go"
	kindOfRun     = "KIND_OF_RUN"
	plainLanguage = "plain language"
	standardError = "standard error"
	broken        = "broken"
	troubleCode   = 2
	settleLimit   = 64
)

var (
	variableShape = regexp.MustCompile(`^\[[a-z]+( [a-z]+)*\]$`)
	numberShape   = regexp.MustCompile(`^-?[0-9]+$`)
	wordsShape    = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	mangleEscapes = strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`, "\t", `\t`)
	tests         = map[string]string{"starts with": ":string:starts_with", "ends with": ":string:ends_with"}
	testWords     = map[string]string{":string:starts_with": "starts with", ":string:ends_with": "ends with"}
	patternVerbs  = []string{"creates fact", "executes instruction", "prints", "shows", "reproduces"}
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
	id     string
	file   string
	head   premise
	body   []premise
	clause ast.Clause
	text   string
}

type reading struct {
	rules    []*rule
	problems []string
	misread  []string
}

type command struct {
	name, tool, input string
}

type section struct {
	pattern  premise
	unrolled bool
}

type derivation struct {
	conditions []ast.Term
	key        string
}

type derivations struct {
	found map[string][]derivation
	best  map[string]derivation
}

type run struct {
	kind     string
	rules    []*rule
	problems []string
	misread  []string
	info     *analysis.ProgramInfo
	order    map[string]int
	model    factstore.SimpleInMemoryStore
	proofs   *derivations
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
	b.WriteString(r.declarations())
	r.order = map[string]int{}
	for i, rl := range r.rules {
		b.WriteString(rl.text + "\n")
		if len(rl.body) == 0 {
			r.order[rl.clause.Head.String()] = i
		}
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

func (r *run) declarations() string {
	var b strings.Builder
	seen := map[string]bool{}
	for _, rl := range r.rules {
		h := rl.head
		if len(rl.body) > 0 || h.name != nameOf("creates fact") || len(h.args) != 2 || !h.args[1].isText() {
			continue
		}
		p, ok := patternOf(h.args[1].text)
		if !ok {
			continue
		}
		key := p.name + "/" + strconv.Itoa(len(p.args))
		if seen[key] {
			continue
		}
		seen[key] = true
		vars := make([]string, len(p.args))
		for i := range vars {
			vars[i] = "A" + strconv.Itoa(i)
		}
		fmt.Fprintf(&b, "Decl %s(%s).\n", p.name, strings.Join(vars, ", "))
	}
	return b.String()
}

func (r *run) evaluate() {
	if r.info == nil {
		r.model = r.factsOnly()
		return
	}
	done := map[string]bool{}
	var live []ast.Atom
	for round := 0; round < settleLimit; round++ {
		r.proofs = &derivations{found: map[string][]derivation{}}
		model, err := r.evalOnce(live)
		r.model = model
		if err != nil {
			r.problem("the rules cannot be evaluated: " + err.Error())
			return
		}
		var fresh []command
		nextLive := r.namings()
		for _, c := range r.commands() {
			if !done[c.key()] {
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
	for _, rl := range r.rules {
		facts = append(facts, rl.facts()...)
	}
	return facts
}

func (rl *rule) facts() []ast.Atom {
	id := ast.String(rl.id)
	facts := []ast.Atom{
		relation("is in", id, ast.String(rl.file)),
		relation("defines", id, ast.String(wordOf(rl.head.name))),
	}
	if law, ok := rl.law(); ok {
		facts = append(facts, relation("lays down", id, ast.String(law)))
	}
	seen := map[string]bool{}
	for _, p := range rl.body {
		if p.shape == relationShape && !seen[p.name] {
			seen[p.name] = true
			facts = append(facts, relation("refers to", id, ast.String(wordOf(p.name))))
		}
	}
	return facts
}

func (rl *rule) law() (string, bool) {
	h := rl.head
	if h.name != nameOf("breaks") || len(h.args) != 2 || !h.args[1].isText() {
		return "", false
	}
	return h.args[1].text, true
}

func (r *run) namings() []ast.Atom {
	var facts []ast.Atom
	seen := map[string]bool{}
	for _, verb := range patternVerbs {
		r.model.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: nameOf(verb), Arity: 2}), func(a ast.Atom) error {
			c, ok := a.Args[1].(ast.Constant)
			if !ok || c.Type != ast.StringType || seen[c.Symbol] {
				return nil
			}
			seen[c.Symbol] = true
			if p, ok := patternOf(c.Symbol); ok {
				facts = append(facts, relation("names", c, ast.String(wordOf(p.name))))
			}
			return nil
		})
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
	return store, engine.EvalProgram(r.info, store, engine.WithDerivationRecorder(r.proofs))
}

func (d *derivations) RuleFired(rule ast.Clause, head ast.Atom, subst unionfind.UnionFind, premiseFacts []ast.Atom) {
	if len(rule.Premises) == 0 {
		return
	}
	conditions := make([]ast.Term, len(rule.Premises))
	keys := make([]string, len(rule.Premises))
	for i, p := range rule.Premises {
		if i < len(premiseFacts) && premiseFacts[i].Predicate.Symbol != "" {
			conditions[i] = premiseFacts[i]
		} else {
			conditions[i] = p.ApplySubst(subst)
		}
		keys[i] = conditions[i].String()
	}
	fact, key := head.String(), strings.Join(keys, "\n")
	for _, known := range d.found[fact] {
		if known.key == key {
			return
		}
	}
	d.found[fact] = append(d.found[fact], derivation{conditions, key})
}

func (d *derivations) LetEmit(ast.Clause, ast.Atom, ast.ConstSubstList, ast.Atom) {}

func (d *derivations) DoEmit(ast.Clause, ast.Atom, []ast.Constant, []ast.Atom, ast.Atom) {}

func (d *derivations) of(fact ast.Atom) (derivation, bool) {
	if d == nil {
		return derivation{}, false
	}
	if d.best == nil {
		d.settle()
	}
	best, ok := d.best[fact.String()]
	return best, ok
}

func (d *derivations) settle() {
	d.best = map[string]derivation{}
	height := map[string]int{}
	for changed := true; changed; {
		changed = false
		for fact, ds := range d.found {
			for _, dv := range ds {
				h, ok := d.height(dv, height)
				if !ok {
					continue
				}
				if old, seen := height[fact]; !seen || h < old || (h == old && dv.key < d.best[fact].key) {
					height[fact], d.best[fact] = h, dv
					changed = true
				}
			}
		}
	}
}

func (d *derivations) height(dv derivation, height map[string]int) (int, bool) {
	h := 1
	for _, c := range dv.conditions {
		a, ok := c.(ast.Atom)
		if !ok {
			continue
		}
		if _, derived := d.found[a.String()]; !derived {
			continue
		}
		below, known := height[a.String()]
		if !known {
			return 0, false
		}
		h = max(h, below+1)
	}
	return h, true
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
	for _, f := range t(r, c.tool, c.input) {
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
	sort.SliceStable(found, func(i, j int) bool { return r.before(found[i], found[j]) })
	return found
}

func (r *run) before(a, b ast.Atom) bool {
	oa, aok := r.order[a.String()]
	ob, bok := r.order[b.String()]
	if aok != bok {
		return aok
	}
	if aok && oa != ob {
		return oa < ob
	}
	return a.String() < b.String()
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
	views := r.facts("prints", ast.String(self), ast.Variable{Symbol: "X"})
	if len(views) == 0 {
		for _, p := range r.problems {
			fmt.Fprintln(out, plainOfAtom(property(p, "a problem")))
		}
		return
	}
	first := true
	for _, v := range views {
		for _, s := range r.sections(v.Args[1]) {
			lines := r.lines(s)
			if len(lines) == 0 {
				continue
			}
			if !first {
				fmt.Fprintln(out)
			}
			first = false
			fmt.Fprintln(out, strings.Join(lines, "\n"))
		}
	}
}

func (r *run) sections(view ast.BaseTerm) []section {
	entries := append(r.facts("shows", view, ast.Variable{Symbol: "X"}), r.facts("reproduces", view, ast.Variable{Symbol: "X"})...)
	if len(entries) == 0 {
		entries = []ast.Atom{relation("shows", view, view)}
	}
	sort.SliceStable(entries, func(i, j int) bool { return r.before(entries[i], entries[j]) })
	var sections []section
	at := map[string]int{}
	for _, e := range entries {
		p, ok := patternOf(textOf(e.Args[1]))
		if !ok {
			continue
		}
		key := p.query().String()
		i, seen := at[key]
		if !seen {
			i = len(sections)
			at[key] = i
			sections = append(sections, section{pattern: p})
		}
		if e.Predicate.Symbol == nameOf("reproduces") {
			sections[i].unrolled = true
		}
	}
	return sections
}

func (r *run) lines(s section) []string {
	type shown struct {
		fact ast.Atom
		line string
	}
	var found []shown
	r.model.GetFacts(s.pattern.query(), func(fact ast.Atom) error {
		found = append(found, shown{fact, plainOfAtom(fact)})
		return nil
	})
	sort.Slice(found, func(i, j int) bool { return naturalLess(found[i].line, found[j].line) })
	var lines []string
	seen := map[string]bool{}
	for _, f := range found {
		if s.unrolled {
			lines = append(lines, r.unroll(f.fact, seen)...)
		} else {
			lines = append(lines, f.line)
		}
	}
	return lines
}

func (r *run) unroll(fact ast.Atom, seen map[string]bool) []string {
	if seen[fact.String()] {
		return nil
	}
	seen[fact.String()] = true
	lines := []string{plainOfAtom(fact)}
	d, ok := r.proofs.of(fact)
	if !ok {
		return lines
	}
	var below []ast.Atom
	for i, c := range d.conditions {
		text, err := plainOfTerm(c)
		if err != nil {
			text = c.String()
		}
		keyword := "and "
		if i == 0 {
			keyword = "if "
		}
		lines = append(lines, "    "+keyword+text)
		if a, ok := c.(ast.Atom); ok {
			if _, derived := r.proofs.of(a); derived {
				below = append(below, a)
			}
		}
	}
	for _, a := range below {
		lines = append(lines, r.unroll(a, seen)...)
	}
	return lines
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
	rl := &rule{id: place(file, group[0]+1), file: file}
	head, err := readPremise(lines[group[0]])
	if err == nil && head.shape != relationShape {
		err = fmt.Errorf("it is a test, not a sentence")
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

func patternOf(pattern string) (premise, bool) {
	line, ok := patternLine(pattern)
	if !ok {
		return premise{}, false
	}
	p, err := readPremise(line)
	if err != nil || p.shape != relationShape {
		return premise{}, false
	}
	return p, true
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
