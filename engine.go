package main

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const brokenCode = 2

type world map[string]string

type site struct {
	path   string
	number int
}

type program struct {
	files   []string
	info    *analysis.ProgramInfo
	facts   []site
	markers map[string]site
}

type step struct {
	key    string
	doing  ast.Constant
	effect string
	kind   string
	gives  map[string][]ast.Constant
}

type outcome struct {
	code    int
	outputs []ast.Atom
	printed []string
	fired   []site
	files   map[string]string
	err     error
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "the machinery starts from exactly one spec")
		os.Exit(brokenCode)
	}
	w, err := readWorld(".")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(brokenCode)
	}
	o := run(w, os.Args[1], nil)
	if o.err != nil {
		fmt.Fprintln(os.Stderr, o.err)
	}
	var outputFiles []string
	for path := range o.files {
		outputFiles = append(outputFiles, path)
	}
	sort.Strings(outputFiles)
	for _, path := range outputFiles {
		if err := os.WriteFile(filepath.FromSlash(path), []byte(o.files[path]), 0o644); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(brokenCode)
		}
	}
	for _, line := range o.printed {
		fmt.Println(line)
	}
	os.Exit(o.code)
}

func readWorld(root string) (world, error) {
	w := world{}
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		content, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		w[filepath.ToSlash(rel)] = string(content)
		return nil
	})
	return w, err
}

func (w world) paths() []string {
	var paths []string
	for path := range w {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	return paths
}

func (w world) with(additions [][2]string) world {
	next := world{}
	for path, content := range w {
		next[path] = content
	}
	for _, addition := range additions {
		content := next[addition[0]]
		if content != "" && !strings.HasSuffix(content, "\n") {
			content += "\n"
		}
		next[addition[0]] = content + addition[1] + "\n"
	}
	return next
}

func load(w world, files []string) (*program, error) {
	p := &program{files: files, markers: map[string]site{}}
	var units []parse.SourceUnit
	var rules []ast.Clause
	var places []site
	prefix := "machinery_fired_"
	for _, file := range files {
		text, ok := w[file]
		if !ok {
			return nil, fmt.Errorf("%s is not in the folder", file)
		}
		for strings.Contains(text, prefix) {
			prefix = "machinery_" + prefix
		}
		unit, err := parse.Unit(strings.NewReader(text))
		if err != nil {
			return nil, fmt.Errorf("%s does not parse: %w", file, err)
		}
		for i, clause := range unit.Clauses {
			place := site{file, i + 1}
			if len(clause.Premises) == 0 && clause.Transform == nil {
				p.facts = append(p.facts, place)
				continue
			}
			rules = append(rules, clause)
			places = append(places, place)
		}
		units = append(units, unit)
	}
	var markers []ast.Clause
	for i, rule := range rules {
		name := fmt.Sprintf("%s%d", prefix, i)
		p.markers[name] = places[i]
		markers = append(markers, ast.Clause{
			Head:     ast.NewAtom(name),
			Premises: append([]ast.Term(nil), rule.Premises...),
		})
	}
	first := units[0]
	units[0] = parse.SourceUnit{
		Decls:   first.Decls,
		Clauses: append(append([]ast.Clause(nil), first.Clauses...), markers...),
	}
	info, err := analysis.Analyze(units, nil)
	if err != nil {
		return nil, fmt.Errorf("the spec and its workflows do not hold together: %w", err)
	}
	p.info = info
	return p, nil
}

func evaluate(p *program, given []ast.Atom) (factstore.FactStore, error) {
	store := factstore.NewSimpleInMemoryStore()
	for _, atom := range given {
		store.Add(atom)
	}
	if err := engine.EvalProgram(p.info, store); err != nil {
		return nil, fmt.Errorf("the spec and its workflows do not evaluate: %w", err)
	}
	return store, nil
}

func factsNamed(store factstore.FactStore, name string, arity int) []ast.Atom {
	var atoms []ast.Atom
	for _, pred := range store.ListPredicates() {
		if pred.Symbol != name || (arity >= 0 && pred.Arity != arity) {
			continue
		}
		store.GetFacts(ast.NewQuery(pred), func(atom ast.Atom) error {
			atoms = append(atoms, atom)
			return nil
		})
	}
	sort.Slice(atoms, func(i, j int) bool { return atoms[i].String() < atoms[j].String() })
	return atoms
}

func constantOf(term ast.BaseTerm) ast.Constant {
	c, _ := term.(ast.Constant)
	return c
}

func stringOf(term ast.BaseTerm) (string, error) {
	return constantOf(term).StringValue()
}

func listOf(c ast.Constant) []ast.Constant {
	var items []ast.Constant
	c.ListValues(func(item ast.Constant) error {
		items = append(items, item)
		return nil
	}, func() error { return nil })
	return items
}

func broken(err error) outcome {
	return outcome{code: brokenCode, err: err}
}

func run(w world, start string, startedBy []string) outcome {
	files := []string{start}
	var given []ast.Atom
	for _, effect := range startedBy {
		given = append(given, ast.NewAtom("started_by", ast.String(effect)))
	}
	done := map[string]bool{}
	var traced []ast.Atom
	seen := map[string]bool{}
	for {
		p, err := load(w, files)
		if err != nil {
			return broken(err)
		}
		store, err := evaluate(p, append(append([]ast.Atom(nil), given...), traced...))
		if err != nil {
			return broken(err)
		}
		more, err := workflowsOf(store, w, files)
		if err != nil {
			return broken(err)
		}
		if len(more) > len(files) {
			files = more
			continue
		}
		steps, err := asked(store)
		if err != nil {
			return broken(err)
		}
		var now, traces []step
		for _, s := range steps {
			if s.kind == "trace" {
				traces = append(traces, s)
			} else if !done[s.key] {
				now = append(now, s)
			}
		}
		if len(now) > 0 {
			got, err := perform(now, w, start, p, store)
			if err != nil {
				return broken(err)
			}
			for _, s := range now {
				done[s.key] = true
			}
			given = append(given, got...)
			continue
		}
		got, err := perform(traces, w, start, p, store)
		if err != nil {
			return broken(err)
		}
		mark := fingerprint(got)
		if mark == fingerprint(traced) {
			return finish(w, p, store)
		}
		if seen[mark] {
			return broken(errors.New("the trace of the folder never settles"))
		}
		seen[mark] = true
		traced = got
	}
}

func fingerprint(atoms []ast.Atom) string {
	var lines []string
	for _, atom := range atoms {
		lines = append(lines, atom.String())
	}
	sort.Strings(lines)
	return strings.Join(lines, "\n")
}

func workflowsOf(store factstore.FactStore, w world, files []string) ([]string, error) {
	known := map[string]bool{}
	for _, file := range files {
		known[file] = true
	}
	more := append([]string(nil), files...)
	for _, atom := range factsNamed(store, "workflow", 1) {
		path, err := stringOf(atom.Args[0])
		if err != nil {
			return nil, fmt.Errorf("a workflow is not named by a string: %v", atom)
		}
		if _, ok := w[path]; ok && !known[path] {
			known[path] = true
			more = append(more, path)
		}
	}
	return more, nil
}

func asked(store factstore.FactStore) ([]step, error) {
	kindsOf := map[string][]string{}
	for _, atom := range factsNamed(store, "effect", 2) {
		effect, err1 := stringOf(atom.Args[0])
		kind, err2 := stringOf(atom.Args[1])
		if err1 != nil || err2 != nil {
			return nil, fmt.Errorf("an effect is not named by strings: %v", atom)
		}
		kindsOf[effect] = append(kindsOf[effect], kind)
	}
	gives := map[string]map[string][]ast.Constant{}
	for _, atom := range factsNamed(store, "gives", 3) {
		key := constantOf(atom.Args[0]).String()
		field, err := stringOf(atom.Args[1])
		if err != nil {
			return nil, fmt.Errorf("a field is not named by a string: %v", atom)
		}
		if gives[key] == nil {
			gives[key] = map[string][]ast.Constant{}
		}
		gives[key][field] = append(gives[key][field], constantOf(atom.Args[2]))
	}
	steps := map[string]*step{}
	var keys []string
	for _, atom := range factsNamed(store, "does", 2) {
		doing := constantOf(atom.Args[0])
		key := doing.String()
		effect, err := stringOf(atom.Args[1])
		if err != nil {
			return nil, fmt.Errorf("an effect is not named by a string: %v", atom)
		}
		if s, ok := steps[key]; ok {
			if s.effect != effect {
				return nil, fmt.Errorf("%s is asked to be done as %q and as %q", key, s.effect, effect)
			}
			continue
		}
		ks := kindsOf[effect]
		if len(ks) != 1 || !kinds[ks[0]] {
			return nil, fmt.Errorf("the effect %q is not one the tools can have: %v", effect, ks)
		}
		steps[key] = &step{key: key, doing: doing, effect: effect, kind: ks[0], gives: gives[key]}
		keys = append(keys, key)
	}
	sort.Strings(keys)
	var ordered []step
	for _, key := range keys {
		ordered = append(ordered, *steps[key])
	}
	return ordered, nil
}

func (s step) one(field string) (string, error) {
	values := s.gives[field]
	if len(values) != 1 {
		return "", fmt.Errorf("%s needs exactly one %q, it was given %d", s.key, field, len(values))
	}
	value, err := values[0].StringValue()
	if err != nil {
		return "", fmt.Errorf("%s needs %q to be a string", s.key, field)
	}
	return value, nil
}

func perform(steps []step, w world, start string, p *program, store factstore.FactStore) ([]ast.Atom, error) {
	results := make([][]ast.Atom, len(steps))
	failures := make([]error, len(steps))
	var wg sync.WaitGroup
	for i, s := range steps {
		wg.Add(1)
		go func() {
			defer wg.Done()
			results[i], failures[i] = do(s, w, start, p, store)
		}()
	}
	wg.Wait()
	var got []ast.Atom
	for i := range steps {
		if failures[i] != nil {
			return nil, failures[i]
		}
		got = append(got, results[i]...)
	}
	return got, nil
}

func finish(w world, p *program, store factstore.FactStore) outcome {
	answers := factsNamed(store, "conforms", 1)
	if len(answers) != 1 {
		return broken(fmt.Errorf("the folder gives %d answers to whether it conforms", len(answers)))
	}
	answer := constantOf(answers[0].Args[0])
	var codes []int64
	for _, atom := range factsNamed(store, "exit_code", 2) {
		if !constantOf(atom.Args[0]).Equals(answer) {
			continue
		}
		code, err := constantOf(atom.Args[1]).NumberValue()
		if err != nil {
			return broken(fmt.Errorf("the exit code of %v is not a number", answer))
		}
		codes = append(codes, code)
	}
	if len(codes) != 1 {
		return broken(fmt.Errorf("the answer %v has %d exit codes", answer, len(codes)))
	}
	outputs, err := outputsOf(store)
	if err != nil {
		return broken(err)
	}
	files, err := written(w, p, store, answers[0])
	if err != nil {
		return broken(err)
	}
	return outcome{code: int(codes[0]), outputs: outputs, printed: printOut(outputs), fired: firedIn(p, store), files: files}
}
