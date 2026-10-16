package main

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const settleWithin = 50

type model struct {
	info  *analysis.ProgramInfo
	store factstore.FactStore
}

type run struct {
	folder   string
	spec     string
	effects  []string
	answer   string
	problems []string
	stated   *model
	full     *model
}

func main() {
	r := &run{folder: ".", answer: "broken"}
	if len(os.Args) > 1 {
		r.spec, r.effects = os.Args[1], os.Args[2:]
	}
	r.check()
	r.tell()
	os.Exit(r.exitCode())
}

func (r *run) fail(format string, args ...any) {
	r.problems = append(r.problems, strings.TrimSpace(fmt.Sprintf(format, args...)))
}

func (r *run) check() {
	src, err := os.ReadFile(filepath.Join(r.folder, r.spec))
	if err != nil {
		r.fail("the spec cannot be read: %v", err)
		return
	}
	if info, err := analysis.Analyze([]parse.SourceUnit{salvage(string(src))}, nil); err == nil {
		r.stated, _ = evaluate(info, nil)
	}
	spec, err := parse.Unit(strings.NewReader(string(src)))
	if err != nil {
		r.fail("%s does not load: %v", r.spec, err)
		return
	}
	units := []parse.SourceUnit{spec}
	for _, path := range r.stated.column("workflow") {
		src, err := os.ReadFile(filepath.Join(r.folder, path))
		if errors.Is(err, fs.ErrNotExist) {
			continue
		}
		if err != nil {
			r.fail("%s cannot be read: %v", path, err)
			return
		}
		unit, err := parse.Unit(strings.NewReader(string(src)))
		if err != nil {
			r.fail("%s does not load: %v", path, err)
			return
		}
		units = append(units, unit)
	}
	info, err := analysis.Analyze(units, nil)
	if err != nil {
		r.fail("the spec and its workflow do not load together: %v", err)
		return
	}
	var started []ast.Atom
	for _, effect := range r.effects {
		started = append(started, ast.NewAtom("started_by", ast.String(effect)))
	}
	got := map[string]ast.Atom{}
	done := map[string][]found{}
	for round := 1; r.full == nil; round++ {
		if round > settleWithin {
			r.fail("the workflow did not settle within %d rounds", settleWithin)
			return
		}
		facts := append([]ast.Atom{}, started...)
		for _, atom := range got {
			facts = append(facts, atom)
		}
		m, err := evaluate(info, facts)
		if err != nil {
			r.fail("the rules cannot be followed: %v", err)
			return
		}
		next, ok := r.perform(m, done)
		if !ok {
			return
		}
		if sameFacts(next, got) {
			r.full = m
		}
		got = next
	}
	answers := r.full.column("conforms")
	if len(answers) != 1 {
		r.fail("the spec gives %d answers instead of one: %v", len(answers), answers)
		return
	}
	r.answer = answers[0]
}

func salvage(src string) parse.SourceUnit {
	if unit, err := parse.Unit(strings.NewReader(src)); err == nil {
		return unit
	}
	var kept []string
	for _, c := range chunksOf(src) {
		if _, err := parse.Unit(strings.NewReader(c.text)); err == nil {
			kept = append(kept, c.text)
		}
	}
	unit, _ := parse.Unit(strings.NewReader(strings.Join(kept, "\n")))
	return unit
}

func evaluate(info *analysis.ProgramInfo, facts []ast.Atom) (*model, error) {
	store := factstore.NewSimpleInMemoryStore()
	for _, fact := range facts {
		store.Add(fact)
	}
	if err := engine.EvalProgram(info, store); err != nil {
		return nil, err
	}
	return &model{info, store}, nil
}

func sameFacts(a, b map[string]ast.Atom) bool {
	if len(a) != len(b) {
		return false
	}
	for key := range a {
		if _, ok := b[key]; !ok {
			return false
		}
	}
	return true
}

func (m *model) facts(name string) [][]ast.Constant {
	if m == nil {
		return nil
	}
	var rows [][]ast.Constant
	for sym := range m.info.Decls {
		if sym.Symbol != name {
			continue
		}
		m.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			row := make([]ast.Constant, len(a.Args))
			for i, arg := range a.Args {
				row[i], _ = arg.(ast.Constant)
			}
			rows = append(rows, row)
			return nil
		})
	}
	key := func(row []ast.Constant) string {
		parts := make([]string, len(row))
		for i, c := range row {
			parts[i] = c.String()
		}
		return strings.Join(parts, "\x00")
	}
	sort.Slice(rows, func(i, j int) bool { return key(rows[i]) < key(rows[j]) })
	return rows
}

func (m *model) column(name string) []string {
	var out []string
	for _, row := range m.facts(name) {
		if len(row) > 0 {
			if s, err := text(row[0]); err == nil {
				out = append(out, s)
			}
		}
	}
	return out
}

type step struct {
	doing   ast.Constant
	tool    string
	input   ast.Constant
	effects []string
	key     string
	results []found
	err     error
	ready   bool
}

func (r *run) perform(m *model, done map[string][]found) (map[string]ast.Atom, bool) {
	gives := map[string]map[string]bool{}
	for _, row := range m.facts("gives") {
		tool, err1 := text(row[0])
		field, err2 := text(row[1])
		if err1 != nil || err2 != nil {
			continue
		}
		if gives[tool] == nil {
			gives[tool] = map[string]bool{}
		}
		gives[tool][field] = true
	}
	effects := map[string][]string{}
	for _, row := range m.facts("effect") {
		if effect, err := text(row[1]); err == nil {
			effects[row[0].String()] = append(effects[row[0].String()], effect)
		}
	}
	var steps []*step
	for _, row := range m.facts("does") {
		name, err := text(row[1])
		if err != nil {
			r.fail("%v is not the name of a tool", row[1])
			return nil, false
		}
		t, ok := tools[name]
		if !ok {
			r.fail("no tool is called %q", name)
			return nil, false
		}
		s := &step{doing: row[0], tool: name, input: row[2], effects: effects[row[0].String()]}
		s.key = strings.Join(append([]string{name, row[2].String()}, s.effects...), "\x00")
		if results, ok := done[s.key]; ok && !t.looksAtTheModel {
			s.results, s.ready = results, true
		}
		steps = append(steps, s)
	}
	limit := make(chan struct{}, max(2, runtime.NumCPU()))
	var wg sync.WaitGroup
	for _, s := range steps {
		if s.ready {
			continue
		}
		wg.Add(1)
		go func() {
			defer wg.Done()
			limit <- struct{}{}
			defer func() { <-limit }()
			w := world{folder: r.folder, effects: s.effects, model: m.store, decls: m.info.Decls}
			s.results, s.err = tools[s.tool].use(w, s.input)
		}()
	}
	wg.Wait()
	got := map[string]ast.Atom{}
	for _, s := range steps {
		if s.err != nil {
			r.fail("%s (%s %v): %v", s.doing, s.tool, s.input, s.err)
			continue
		}
		done[s.key] = s.results
		for _, f := range s.results {
			if gives[s.tool][f.field] {
				atom := ast.NewAtom("got", s.doing, ast.String(f.field), f.value)
				got[atom.String()] = atom
			}
		}
	}
	return got, len(r.problems) == 0
}

func (r *run) exitCode() int {
	for _, m := range []*model{r.full, r.stated} {
		for _, row := range m.facts("exit_code") {
			if answer, err := text(row[0]); err == nil && answer == r.answer {
				if code, err := row[1].NumberValue(); err == nil {
					return int(code)
				}
			}
		}
	}
	fmt.Fprintf(os.Stderr, "the spec does not say how to exit when the answer is %q\n", r.answer)
	return 2
}
