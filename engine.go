package main

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/functional"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	brokenAnswer = "broken"
	firedMark    = "engine_saw_fire"
	maxRounds    = 64
)

type source struct {
	path string
	unit parse.SourceUnit
}

type ruleAt struct {
	path string
	rule string
}

type outcome struct {
	dir      string
	store    factstore.FactStore
	answer   string
	code     int
	problems []string
	rounds   int
}

type machine struct {
	dir     string
	spec    string
	effect  string
	sources []source
	program *analysis.ProgramInfo
	strata  []analysis.Nodeset
	layers  map[ast.PredicateSym]int
	marks   []ruleAt
	facts   []ruleAt
	missing []string

	mu    sync.Mutex
	fired map[string][]string
	memo  map[string]result
}

type result struct {
	findings []finding
	err      error
}

func main() {
	spec := ""
	if len(os.Args) > 1 {
		spec = os.Args[1]
	}
	o := run(".", spec, "a command")
	written, err := writeReport(o)
	if err != nil {
		o.problems = append(o.problems, "the report: "+err.Error())
	}
	for _, p := range o.problems {
		fmt.Fprintln(os.Stderr, "problem:", p)
	}
	fmt.Printf("conforms: %s\n", o.answer)
	if written != "" {
		fmt.Printf("report: %s\n", written)
	}
	os.Exit(o.code)
}

func run(dir, spec, effect string) outcome {
	m := &machine{
		dir:    dir,
		spec:   spec,
		effect: effect,
		fired:  map[string][]string{},
		memo:   map[string]result{},
	}
	if err := m.load(); err != nil {
		return m.broken(err, nil)
	}
	return m.settle()
}

func (m *machine) path(rel string) (string, error) {
	if rel == "" {
		return "", errors.New("no path given")
	}
	if !filepath.IsLocal(rel) && rel != "." {
		return "", fmt.Errorf("%s is outside the folder", rel)
	}
	return filepath.Join(m.dir, filepath.FromSlash(rel)), nil
}

func (m *machine) read(rel string) (source, error) {
	full, err := m.path(rel)
	if err != nil {
		return source{}, err
	}
	data, err := os.ReadFile(full)
	if err != nil {
		return source{}, err
	}
	unit, err := parse.Unit(strings.NewReader(string(data)))
	if err != nil {
		return source{}, fmt.Errorf("%s does not parse: %s", rel, strings.TrimSpace(err.Error()))
	}
	return source{path: rel, unit: unit}, nil
}

func (m *machine) load() error {
	if m.spec == "" {
		return errors.New("no spec was named")
	}
	spec, err := m.read(m.spec)
	if err != nil {
		return err
	}
	m.sources = []source{spec}
	loaded := map[string]bool{filepath.Clean(m.spec): true}
	for _, w := range m.workflows(spec.unit) {
		full, err := m.path(w)
		if err != nil {
			m.missing = append(m.missing, fmt.Sprintf("workflow %s: %v", w, err))
			continue
		}
		if loaded[filepath.Clean(w)] {
			continue
		}
		loaded[filepath.Clean(w)] = true
		if _, err := os.Stat(full); err != nil {
			m.missing = append(m.missing, fmt.Sprintf("workflow %s is not in the folder", w))
			continue
		}
		src, err := m.read(w)
		if err != nil {
			return err
		}
		m.sources = append(m.sources, src)
	}
	return m.build()
}

func (m *machine) workflows(spec parse.SourceUnit) []string {
	query := ast.NewQuery(ast.PredicateSym{Symbol: "workflow", Arity: 1})
	var facts []ast.Atom
	program, err := analysis.Analyze([]parse.SourceUnit{spec}, nil)
	if err == nil {
		var store factstore.FactStore
		if store, err = evaluate(program, nil, nil, nil); err == nil {
			store.GetFacts(query, func(a ast.Atom) error {
				facts = append(facts, a)
				return nil
			})
		}
	}
	if err != nil {
		for _, c := range spec.Clauses {
			if len(c.Premises) == 0 && c.Head.Predicate == query.Predicate {
				facts = append(facts, c.Head)
			}
		}
	}
	var paths []string
	for _, a := range facts {
		p, err := text(a.Args[0])
		if err != nil {
			m.missing = append(m.missing, fmt.Sprintf("%s does not name a workflow file", a))
			continue
		}
		paths = append(paths, p)
	}
	return sorted(paths)
}

func (m *machine) build() error {
	var units []parse.SourceUnit
	var marks []ast.Clause
	for _, src := range m.sources {
		units = append(units, src.unit)
		for _, c := range src.unit.Clauses {
			at := ruleAt{path: src.path, rule: c.String()}
			if len(c.Premises) == 0 {
				m.facts = append(m.facts, at)
				continue
			}
			premises := make([]ast.Term, len(c.Premises))
			copy(premises, c.Premises)
			head := ast.NewAtom(firedMark, ast.Number(int64(len(m.marks))))
			marks = append(marks, ast.NewClause(head, premises))
			m.marks = append(m.marks, at)
		}
	}
	units = append(units, parse.SourceUnit{Clauses: marks})
	program, err := analysis.Analyze(units, nil)
	if err != nil {
		return fmt.Errorf("the spec and its workflows do not make a program: %v", err)
	}
	strata, layers, err := analysis.Stratify(analysis.Program{
		EdbPredicates: program.EdbPredicates,
		IdbPredicates: program.IdbPredicates,
		Rules:         program.Rules,
	})
	if err != nil {
		return fmt.Errorf("the program cannot be layered: %v", err)
	}
	m.program, m.strata, m.layers = program, strata, layers
	return nil
}

func evaluate(program *analysis.ProgramInfo, strata []analysis.Nodeset, layers map[ast.PredicateSym]int, given []ast.Atom) (store factstore.FactStore, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("evaluation failed: %v", r)
		}
	}()
	if strata == nil {
		strata, layers, err = analysis.Stratify(analysis.Program{
			EdbPredicates: program.EdbPredicates,
			IdbPredicates: program.IdbPredicates,
			Rules:         program.Rules,
		})
		if err != nil {
			return nil, err
		}
	}
	store = factstore.NewSimpleInMemoryStore()
	for _, a := range given {
		store.Add(a)
	}
	_, err = engine.EvalStratifiedProgramWithStats(program, strata, layers, store)
	return store, err
}

type step struct {
	name  ast.Constant
	tool  string
	input ast.Constant
}

func (m *machine) settle() outcome {
	got := map[string]ast.Atom{}
	problems := map[string]bool{}
	settled := false
	for round := 1; ; round++ {
		store, err := evaluate(m.program, m.strata, m.layers, m.given(got, problems))
		if err != nil {
			return m.broken(err, problems)
		}
		if settled {
			return m.finish(store, problems, round)
		}
		m.see(store)
		steps, stepProblems := m.steps(store)
		nextGot, nextProblems := m.work(steps)
		for p := range stepProblems {
			nextProblems[p] = true
		}
		if sameAtoms(got, nextGot) && sameSet(problems, nextProblems) {
			return m.finish(store, problems, round)
		}
		got, problems = nextGot, nextProblems
		if round >= maxRounds {
			problems[fmt.Sprintf("the workflow did not settle after %d rounds", maxRounds)] = true
			settled = true
		}
	}
}

func (m *machine) given(got map[string]ast.Atom, problems map[string]bool) []ast.Atom {
	atoms := []ast.Atom{ast.NewAtom("started_by", ast.String(m.effect))}
	for _, p := range m.allProblems(problems) {
		atoms = append(atoms, ast.NewAtom("problem", ast.String(p)))
	}
	for _, a := range got {
		atoms = append(atoms, a)
	}
	return atoms
}

func (m *machine) allProblems(problems map[string]bool) []string {
	all := append([]string{}, m.missing...)
	for p := range problems {
		all = append(all, p)
	}
	sort.Strings(all)
	return all
}

func (m *machine) see(store factstore.FactStore) {
	fired := map[string][]string{}
	for _, f := range m.facts {
		fired[f.path] = append(fired[f.path], f.rule)
	}
	store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: firedMark, Arity: 1}), func(a ast.Atom) error {
		c, ok := a.Args[0].(ast.Constant)
		if !ok {
			return nil
		}
		n, err := c.NumberValue()
		if err != nil || n < 0 || int(n) >= len(m.marks) {
			return nil
		}
		at := m.marks[n]
		fired[at.path] = append(fired[at.path], at.rule)
		return nil
	})
	m.mu.Lock()
	m.fired = fired
	m.mu.Unlock()
}

func (m *machine) firedIn(path string) []string {
	m.mu.Lock()
	defer m.mu.Unlock()
	return append([]string{}, m.fired[path]...)
}

func (m *machine) steps(store factstore.FactStore) ([]step, map[string]bool) {
	var steps []step
	problems := map[string]bool{}
	store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "does", Arity: 3}), func(a ast.Atom) error {
		name, _ := a.Args[0].(ast.Constant)
		input, _ := a.Args[2].(ast.Constant)
		tool, err := text(a.Args[1])
		if err != nil {
			problems[fmt.Sprintf("step %s names its tool with %s, which is not a name", name, a.Args[1])] = true
			return nil
		}
		steps = append(steps, step{name: name, tool: tool, input: input})
		return nil
	})
	return steps, problems
}

func (m *machine) work(steps []step) (map[string]ast.Atom, map[string]bool) {
	got := map[string]ast.Atom{}
	problems := map[string]bool{}
	var mu sync.Mutex
	var wg sync.WaitGroup
	slots := make(chan struct{}, 8)
	for _, s := range steps {
		wg.Add(1)
		go func(s step) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			findings, err := m.use(s)
			mu.Lock()
			defer mu.Unlock()
			if err != nil {
				problems[fmt.Sprintf("step %s: %v", s.name, err)] = true
			}
			for _, f := range findings {
				a := ast.NewAtom("got", s.name, ast.String(f.field), f.value)
				got[a.String()] = a
			}
		}(s)
	}
	wg.Wait()
	return got, problems
}

func (m *machine) use(s step) (findings []finding, err error) {
	t, ok := tools[s.tool]
	if !ok {
		return nil, fmt.Errorf("there is no tool called %q", s.tool)
	}
	key := s.tool + "\x00" + s.input.String()
	if t.remembers {
		m.mu.Lock()
		r, done := m.memo[key]
		m.mu.Unlock()
		if done {
			return r.findings, r.err
		}
	}
	func() {
		defer func() {
			if r := recover(); r != nil {
				err = fmt.Errorf("the tool %q failed: %v", s.tool, r)
			}
		}()
		findings, err = t.use(m, s.input)
	}()
	if t.remembers {
		m.mu.Lock()
		m.memo[key] = result{findings, err}
		m.mu.Unlock()
	}
	return findings, err
}

func (m *machine) finish(store factstore.FactStore, problems map[string]bool, rounds int) outcome {
	o := outcome{dir: m.dir, store: store, problems: m.allProblems(problems), rounds: rounds}
	var answers []string
	store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "conforms", Arity: 1}), func(a ast.Atom) error {
		if s, err := text(a.Args[0]); err == nil {
			answers = append(answers, s)
		}
		return nil
	})
	sort.Strings(answers)
	switch len(answers) {
	case 1:
		o.answer = answers[0]
	case 0:
		o.problems = append(o.problems, "the program does not say whether the folder conforms")
	default:
		o.problems = append(o.problems, "the program gives more than one answer: "+strings.Join(answers, ", "))
	}
	o.code = m.exitCode(&o)
	return o
}

func (m *machine) broken(cause error, problems map[string]bool) outcome {
	o := outcome{dir: m.dir, answer: brokenAnswer}
	o.problems = append([]string{cause.Error()}, m.allProblems(problems)...)
	store := factstore.NewSimpleInMemoryStore()
	for _, f := range m.salvage() {
		store.Add(f)
	}
	for _, p := range o.problems {
		store.Add(ast.NewAtom("problem", ast.String(p)))
	}
	o.store = store
	o.code = m.exitCode(&o)
	return o
}

func (m *machine) salvage() []ast.Atom {
	full, err := m.path(m.spec)
	if err != nil {
		return nil
	}
	data, err := os.ReadFile(full)
	if err != nil {
		return nil
	}
	var facts []ast.Atom
	for _, line := range strings.Split(string(data), "\n") {
		if strings.TrimSpace(line) == "" {
			continue
		}
		unit, err := parse.Unit(strings.NewReader(line))
		if err != nil {
			continue
		}
		for _, c := range unit.Clauses {
			if len(c.Premises) != 0 || c.Transform != nil {
				continue
			}
			f, err := functional.EvalAtom(c.Head, nil)
			if err != nil || !f.IsGround() {
				continue
			}
			facts = append(facts, f)
		}
	}
	return facts
}

func (m *machine) exitCode(o *outcome) int {
	code := -1
	o.store.GetFacts(ast.NewAtom("exit_code", ast.String(o.answer), ast.Variable{Symbol: "Code"}), func(a ast.Atom) error {
		if c, ok := a.Args[1].(ast.Constant); ok {
			if n, err := c.NumberValue(); err == nil && code < 0 {
				code = int(n)
			}
		}
		return nil
	})
	if code < 0 {
		o.problems = append(o.problems, fmt.Sprintf("the program gives no exit code for the answer %q", o.answer))
		return 1
	}
	return code
}

func text(t ast.BaseTerm) (string, error) {
	c, ok := t.(ast.Constant)
	if !ok {
		return "", fmt.Errorf("%v is not a constant", t)
	}
	return c.StringValue()
}

func sameAtoms(a, b map[string]ast.Atom) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if _, ok := b[k]; !ok {
			return false
		}
	}
	return true
}

func sameSet(a, b map[string]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}
