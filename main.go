package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"html"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode"
	"unicode/utf8"

	antlr "github.com/antlr4-go/antlr/v4"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/parse/gen"
)

const brokenCode = 2

var kinds = map[string]bool{"list": true, "read": true, "parse": true, "start": true, "trace": true}

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

type placed struct {
	line int
	text string
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "the machinery starts from exactly one program")
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

func linesOf(content string) []string {
	if content == "" {
		return nil
	}
	return strings.Split(strings.TrimSuffix(content, "\n"), "\n")
}

func parseText(text string) (parse.SourceUnit, []placed, error) {
	unit, err := parse.Unit(strings.NewReader(text))
	if err != nil {
		return parse.SourceUnit{}, nil, err
	}
	lexer := gen.NewMangleLexer(antlr.NewInputStream(text))
	lexer.RemoveErrorListeners()
	parser := gen.NewMangleParser(antlr.NewCommonTokenStream(lexer, antlr.TokenDefaultChannel))
	parser.RemoveErrorListeners()
	runes := []rune(text)
	var places []placed
	for _, clause := range parser.Start_().Program().AllClause() {
		first, last := clause.GetStart(), clause.GetStop()
		place := placed{line: first.GetLine()}
		if last != nil {
			if from, to := first.GetStart(), last.GetStop(); from >= 0 && from <= to && to < len(runes) {
				place.text = string(runes[from : to+1])
			}
		}
		places = append(places, place)
	}
	if len(places) != len(unit.Clauses) {
		return parse.SourceUnit{}, nil, errors.New("the clauses of the program could not be placed on lines")
	}
	return unit, places, nil
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
			return nil, fmt.Errorf("%s is not in the world", file)
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
		return nil, fmt.Errorf("the program does not hold together: %w", err)
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
		return nil, fmt.Errorf("the program does not evaluate: %w", err)
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

func firedIn(p *program, store factstore.FactStore) []site {
	fired := append([]site(nil), p.facts...)
	for name, place := range p.markers {
		if store.Contains(ast.NewAtom(name)) {
			fired = append(fired, place)
		}
	}
	sort.Slice(fired, func(i, j int) bool {
		if fired[i].path != fired[j].path {
			return fired[i].path < fired[j].path
		}
		return fired[i].number < fired[j].number
	})
	return fired
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
		more, err := programsOf(store, w, files)
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
			return broken(errors.New("the trace of the world never settles"))
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

func programsOf(store factstore.FactStore, w world, files []string) ([]string, error) {
	known := map[string]bool{}
	for _, file := range files {
		known[file] = true
	}
	more := append([]string(nil), files...)
	for _, atom := range factsNamed(store, "machine_program", 1) {
		path, err := stringOf(atom.Args[0])
		if err != nil {
			return nil, fmt.Errorf("a machine program is not named by a string: %v", atom)
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
			return nil, fmt.Errorf("the effect %q is not one the machinery can have: %v", effect, ks)
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

func do(s step, w world, start string, p *program, store factstore.FactStore) ([]ast.Atom, error) {
	var got []ast.Atom
	give := func(field string, value ast.Constant) {
		got = append(got, ast.NewAtom("got", s.doing, ast.String(field), value))
	}
	switch s.kind {
	case "list":
		for _, path := range w.paths() {
			give("file", ast.String(path))
		}
	case "read":
		path, err := s.one("path")
		if err != nil {
			return nil, err
		}
		content, ok := w[path]
		if !ok {
			return nil, nil
		}
		lines := linesOf(content)
		for i, line := range lines {
			give("line", ast.List([]ast.Constant{ast.Number(int64(i + 1)), ast.String(line)}))
		}
		give("lines", ast.Number(int64(len(lines))))
	case "parse":
		path, err := s.one("path")
		if err != nil {
			return nil, err
		}
		content, ok := w[path]
		if !ok {
			return nil, nil
		}
		unit, places, err := parseText(content)
		if err != nil {
			return nil, nil
		}
		for i, clause := range unit.Clauses {
			number := ast.Number(int64(i + 1))
			line := ast.Number(int64(places[i].line))
			give("clause", ast.List([]ast.Constant{number, line, ast.String(clause.Head.Predicate.Symbol)}))
			for j, arg := range clause.Head.Args {
				if c, ok := arg.(ast.Constant); ok {
					give("argument", ast.List([]ast.Constant{number, ast.Number(int64(j + 1)), c}))
				}
			}
		}
	case "start":
		var additions [][2]string
		for _, value := range s.gives["adds"] {
			items := listOf(value)
			if len(items) != 2 {
				return nil, fmt.Errorf("%s adds something that is not a path and a line: %v", s.key, value)
			}
			path, err1 := items[0].StringValue()
			line, err2 := items[1].StringValue()
			if err1 != nil || err2 != nil {
				return nil, fmt.Errorf("%s adds something that is not a path and a line: %v", s.key, value)
			}
			additions = append(additions, [2]string{path, line})
		}
		sort.Slice(additions, func(i, j int) bool {
			if additions[i][0] != additions[j][0] {
				return additions[i][0] < additions[j][0]
			}
			return additions[i][1] < additions[j][1]
		})
		o := run(w.with(additions), start, []string{s.effect})
		give("exit code", ast.Number(int64(o.code)))
		for _, atom := range o.outputs {
			fact := []ast.Constant{ast.String(atom.Predicate.Symbol)}
			for _, arg := range atom.Args {
				fact = append(fact, constantOf(arg))
			}
			give("output", ast.List(fact))
		}
		for _, place := range o.fired {
			give("fired", ast.List([]ast.Constant{ast.String(place.path), ast.Number(int64(place.number))}))
		}
	case "trace":
		for _, place := range firedIn(p, store) {
			give("fired", ast.List([]ast.Constant{ast.String(place.path), ast.Number(int64(place.number))}))
		}
	}
	return got, nil
}

func finish(w world, p *program, store factstore.FactStore) outcome {
	answers := factsNamed(store, "answer", 1)
	if len(answers) != 1 {
		return broken(fmt.Errorf("the world gives %d answers", len(answers)))
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
	var outputs []ast.Atom
	for _, atom := range factsNamed(store, "output", 1) {
		name, err := stringOf(atom.Args[0])
		if err != nil {
			return broken(fmt.Errorf("the machinery cannot give the output %v", atom))
		}
		outputs = append(outputs, factsNamed(store, name, -1)...)
	}
	sort.Slice(outputs, func(i, j int) bool { return outputs[i].String() < outputs[j].String() })
	printed, err := printOut(store, outputs)
	if err != nil {
		return broken(err)
	}
	files, err := written(w, p, store, answers[0])
	if err != nil {
		return broken(err)
	}
	return outcome{code: int(codes[0]), outputs: outputs, printed: printed, fired: firedIn(p, store), files: files}
}

var placeholder = regexp.MustCompile(`\{([0-9]+)\}`)

func printOut(store factstore.FactStore, outputs []ast.Atom) ([]string, error) {
	languages := factsNamed(store, "printed_in", 1)
	if len(languages) != 1 {
		return nil, fmt.Errorf("the world prints in %d languages", len(languages))
	}
	language, err := stringOf(languages[0].Args[0])
	if err != nil {
		return nil, fmt.Errorf("the language the world prints in is not named by a string: %v", languages[0])
	}
	var printed []string
	switch language {
	case "mangle":
		for _, atom := range outputs {
			printed = append(printed, atom.String()+".")
		}
	case "english":
		readings := map[string][]ast.Constant{}
		for _, atom := range factsNamed(store, "reads_as", 2) {
			word, err := stringOf(atom.Args[0])
			if err != nil {
				return nil, fmt.Errorf("a reading is not of a word named by a string: %v", atom)
			}
			readings[word] = append(readings[word], constantOf(atom.Args[1]))
		}
		for _, atom := range outputs {
			line, err := inEnglish(atom, readings[atom.Predicate.Symbol])
			if err != nil {
				return nil, err
			}
			printed = append(printed, line)
		}
	default:
		return nil, fmt.Errorf("the machinery cannot print in %q", language)
	}
	return printed, nil
}

func inEnglish(atom ast.Atom, readings []ast.Constant) (string, error) {
	word := atom.Predicate.Symbol
	if len(readings) != 1 {
		return "", fmt.Errorf("the word %s has %d readings, so %v cannot be printed in english", word, len(readings), atom)
	}
	reading, err := readings[0].StringValue()
	if err != nil {
		return "", fmt.Errorf("the reading of the word %s is not a string: %v", word, readings[0])
	}
	var failure error
	line := placeholder.ReplaceAllStringFunc(reading, func(hole string) string {
		position, err := strconv.Atoi(placeholder.FindStringSubmatch(hole)[1])
		if err != nil || position < 1 || position > len(atom.Args) {
			failure = fmt.Errorf("the reading of the word %s asks for {%d}, but %v has %d arguments", word, position, atom, len(atom.Args))
			return hole
		}
		value := constantOf(atom.Args[position-1])
		if text, err := value.StringValue(); err == nil {
			return text
		}
		return value.DisplayString()
	})
	if failure != nil {
		return "", failure
	}
	return line, nil
}

type view struct {
	w         world
	readings  map[string]string
	negations map[string]string
	sources   map[string]*source
}

type source struct {
	unit   parse.SourceUnit
	places []placed
}

type ruleRef struct {
	key  string
	path string
	line int64
	ok   bool
}

type concept struct {
	name   string
	titles []string
	rules  []ruleRef
	cases  []string
}

type ruleData struct {
	Summary string   `json:"summary"`
	Source  string   `json:"source"`
	Words   []string `json:"words"`
}

type wordData struct {
	Summary string   `json:"summary"`
	Rules   []string `json:"rules"`
}

type pageData struct {
	Opens     string              `json:"opens"`
	Explained string              `json:"explained"`
	Rules     map[string]ruleData `json:"rules"`
	Words     map[string]wordData `json:"words"`
}

func written(w world, p *program, store factstore.FactStore, answer ast.Atom) (map[string]string, error) {
	targets := factsNamed(store, "output_file", 1)
	if len(targets) == 0 {
		return nil, nil
	}
	programs := map[string]bool{}
	for _, file := range p.files {
		programs[file] = true
	}
	content, err := render(w, p, store, answer)
	if err != nil {
		return nil, err
	}
	files := map[string]string{}
	for _, atom := range targets {
		path, err := stringOf(atom.Args[0])
		if err != nil {
			return nil, fmt.Errorf("an output file is not named by a string: %v", atom)
		}
		if !filepath.IsLocal(filepath.FromSlash(path)) {
			return nil, fmt.Errorf("the machinery writes only inside the world, not to %q", path)
		}
		path = filepath.ToSlash(filepath.Clean(filepath.FromSlash(path)))
		if programs[path] {
			return nil, fmt.Errorf("the machinery will not write over the program %s", path)
		}
		files[path] = content
	}
	return files, nil
}

func newView(w world, store factstore.FactStore) *view {
	v := &view{w: w, readings: map[string]string{}, negations: map[string]string{}, sources: map[string]*source{}}
	for word, texts := range textPairs(store, "reads_as") {
		if len(texts) == 1 {
			v.readings[word] = texts[0]
		}
	}
	for phrase, texts := range textPairs(store, "negation") {
		if len(texts) == 1 && phrase != "" {
			v.negations[phrase] = texts[0]
		}
	}
	return v
}

func textPairs(store factstore.FactStore, name string) map[string][]string {
	pairs := map[string][]string{}
	for _, atom := range factsNamed(store, name, 2) {
		first, err1 := stringOf(atom.Args[0])
		second, err2 := stringOf(atom.Args[1])
		if err1 == nil && err2 == nil {
			pairs[first] = append(pairs[first], second)
		}
	}
	return pairs
}

func textOf(c ast.Constant) string {
	if text, err := c.StringValue(); err == nil {
		return text
	}
	return c.DisplayString()
}

func refOf(rule ast.Constant) ruleRef {
	ref := ruleRef{key: rule.DisplayString()}
	if items := listOf(rule); len(items) == 2 {
		path, err1 := items[0].StringValue()
		line, err2 := items[1].NumberValue()
		if err1 == nil && err2 == nil {
			ref = ruleRef{key: fmt.Sprintf("%s:%d", path, line), path: path, line: line, ok: true}
		}
	}
	return ref
}

func before(a, b ruleRef) bool {
	if a.path != b.path {
		return a.path < b.path
	}
	if a.line != b.line {
		return a.line < b.line
	}
	return a.key < b.key
}

func (c *concept) title() string {
	if len(c.titles) == 0 {
		return c.name
	}
	return strings.Join(c.titles, " · ")
}

func (v *view) source(path string) *source {
	if s, ok := v.sources[path]; ok {
		return s
	}
	var s *source
	if text, ok := v.w[path]; ok {
		if unit, places, err := parseText(text); err == nil {
			s = &source{unit: unit, places: places}
		}
	}
	v.sources[path] = s
	return s
}

func (v *view) clause(ref ruleRef) (ast.Clause, string, bool) {
	if !ref.ok {
		return ast.Clause{}, "", false
	}
	s := v.source(ref.path)
	if s == nil {
		return ast.Clause{}, "", false
	}
	for i, place := range s.places {
		if int64(place.line) == ref.line {
			return s.unit.Clauses[i], place.text, true
		}
	}
	return ast.Clause{}, "", false
}

func (v *view) label(word string) string {
	if reading, ok := v.readings[word]; ok {
		if from := strings.Index(reading, "{1}"); from >= 0 {
			if to := strings.Index(reading[from:], "{2}"); to >= 0 {
				if text := strings.TrimSpace(reading[from+3 : from+to]); text != "" {
					return text
				}
			}
		}
	}
	return word
}

func codeHTML(text string) string {
	return "<code>" + html.EscapeString(text) + "</code>"
}

func isWordRune(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_'
}

func standsAlone(text string, at, size int) bool {
	if at > 0 {
		if r, _ := utf8.DecodeLastRuneInString(text[:at]); isWordRune(r) {
			return false
		}
	}
	if at+size < len(text) {
		if r, _ := utf8.DecodeRuneInString(text[at+size:]); isWordRune(r) {
			return false
		}
	}
	return true
}

func (v *view) negate(reading string) (string, bool) {
	at, size, phrase := -1, 0, ""
	for candidate := range v.negations {
		for from := 0; from <= len(reading); {
			i := strings.Index(reading[from:], candidate)
			if i < 0 {
				break
			}
			i += from
			if standsAlone(reading, i, len(candidate)) && (at < 0 || i < at || (i == at && len(candidate) > size)) {
				at, size, phrase = i, len(candidate), candidate
			}
			from = i + 1
		}
	}
	if at < 0 {
		return "", false
	}
	return reading[:at] + v.negations[phrase] + reading[at+size:], true
}

func (v *view) term(t ast.BaseTerm) string {
	switch t := t.(type) {
	case ast.Variable:
		if t.Symbol == "_" {
			return `<var class="any">something</var>`
		}
		return "<var>" + html.EscapeString(t.Symbol) + "</var>"
	case ast.Constant:
		return `<span class="value">` + html.EscapeString(textOf(t)) + "</span>"
	}
	return codeHTML(t.String())
}

func (v *view) atom(atom ast.Atom, negated bool) string {
	code := atom.String()
	if negated {
		code = "!" + code
	}
	reading, ok := v.readings[atom.Predicate.Symbol]
	if !ok {
		return codeHTML(code)
	}
	if negated {
		if reading, ok = v.negate(reading); !ok {
			return codeHTML(code)
		}
	}
	var b strings.Builder
	last := 0
	for _, hole := range placeholder.FindAllStringSubmatchIndex(reading, -1) {
		position, err := strconv.Atoi(reading[hole[2]:hole[3]])
		if err != nil || position < 1 || position > len(atom.Args) {
			return codeHTML(code)
		}
		b.WriteString(html.EscapeString(reading[last:hole[0]]))
		b.WriteString(v.term(atom.Args[position-1]))
		last = hole[1]
	}
	b.WriteString(html.EscapeString(reading[last:]))
	return `<span class="atom">` + b.String() + "</span>"
}

func (v *view) premise(t ast.Term) string {
	switch t := t.(type) {
	case ast.Atom:
		return v.atom(t, false)
	case ast.NegAtom:
		return v.atom(t.Atom, true)
	}
	return codeHTML(t.String())
}

func (v *view) sentence(c ast.Clause) string {
	var b strings.Builder
	b.WriteString(v.atom(c.Head, false))
	for i, premise := range c.Premises {
		if i == 0 {
			b.WriteString(` <span class="join">when</span> `)
		} else {
			b.WriteString(` <span class="join">and</span> `)
		}
		b.WriteString(v.premise(premise))
	}
	if c.Transform != nil {
		b.WriteString(" " + codeHTML("|> "+c.Transform.String()))
	}
	return b.String()
}

func (v *view) rule(ref ruleRef, words []string) ruleData {
	data := ruleData{Summary: `<span class="sentence">` + html.EscapeString(ref.key) + "</span>", Words: words}
	if clause, text, ok := v.clause(ref); ok {
		data.Summary = `<span class="sentence">` + v.sentence(clause) + `</span><span class="site">` + html.EscapeString(ref.key) + "</span>"
		data.Source = text
	}
	return data
}

func (v *view) word(name string) string {
	var b strings.Builder
	b.WriteString(`<span class="sentence"><code class="word">` + html.EscapeString(name) + "</code>")
	if reading, ok := v.readings[name]; ok {
		b.WriteString(` <span class="reading">`)
		last := 0
		for _, hole := range placeholder.FindAllStringSubmatchIndex(reading, -1) {
			b.WriteString(html.EscapeString(reading[last:hole[0]]))
			b.WriteString(`<span class="hole">` + html.EscapeString(reading[hole[2]:hole[3]]) + "</span>")
			last = hole[1]
		}
		b.WriteString(html.EscapeString(reading[last:]) + "</span>")
	}
	b.WriteString("</span>")
	return b.String()
}

func render(w world, p *program, store factstore.FactStore, answer ast.Atom) (string, error) {
	v := newView(w, store)
	refs := map[string]ruleRef{}
	note := func(rule ast.Constant) ruleRef {
		ref := refOf(rule)
		refs[ref.key] = ref
		return ref
	}
	opens := map[string]map[string]bool{}
	explains := map[string]map[string]bool{}
	for _, atom := range factsNamed(store, "opens_into", 2) {
		ref := note(constantOf(atom.Args[0]))
		word := textOf(constantOf(atom.Args[1]))
		if opens[ref.key] == nil {
			opens[ref.key] = map[string]bool{}
		}
		opens[ref.key][word] = true
		if explains[word] == nil {
			explains[word] = map[string]bool{}
		}
	}
	for _, atom := range factsNamed(store, "explained_by", 2) {
		word := textOf(constantOf(atom.Args[0]))
		ref := note(constantOf(atom.Args[1]))
		if explains[word] == nil {
			explains[word] = map[string]bool{}
		}
		explains[word][ref.key] = true
	}
	concepts := map[string]*concept{}
	conceptOf := func(term ast.BaseTerm) *concept {
		name := textOf(constantOf(term))
		if concepts[name] == nil {
			concepts[name] = &concept{name: name}
		}
		return concepts[name]
	}
	for _, atom := range factsNamed(store, "title", 2) {
		c := conceptOf(atom.Args[0])
		c.titles = append(c.titles, textOf(constantOf(atom.Args[1])))
	}
	for _, atom := range factsNamed(store, "shows", 2) {
		c := conceptOf(atom.Args[0])
		c.rules = append(c.rules, note(constantOf(atom.Args[1])))
	}
	for _, atom := range factsNamed(store, "shows_case", 2) {
		c := conceptOf(atom.Args[0])
		c.cases = append(c.cases, textOf(constantOf(atom.Args[1])))
	}
	data := pageData{
		Opens:     html.EscapeString(v.label("opens_into")),
		Explained: html.EscapeString(v.label("explained_by")),
		Rules:     map[string]ruleData{},
		Words:     map[string]wordData{},
	}
	for key, ref := range refs {
		words := []string{}
		for word := range opens[key] {
			words = append(words, word)
		}
		sort.Strings(words)
		data.Rules[key] = v.rule(ref, words)
	}
	for word, keys := range explains {
		var listed []ruleRef
		for key := range keys {
			listed = append(listed, refs[key])
		}
		sort.Slice(listed, func(i, j int) bool { return before(listed[i], listed[j]) })
		rules := []string{}
		for _, ref := range listed {
			rules = append(rules, ref.key)
		}
		data.Words[word] = wordData{Summary: v.word(word), Rules: rules}
	}
	var ordered []*concept
	for _, c := range concepts {
		sort.Strings(c.titles)
		sort.Strings(c.cases)
		sort.Slice(c.rules, func(i, j int) bool { return before(c.rules[i], c.rules[j]) })
		ordered = append(ordered, c)
	}
	rank := func(c *concept) int {
		for _, ref := range c.rules {
			if clause, _, ok := v.clause(ref); ok && clause.Head.Predicate.Symbol == "answer" {
				return 0
			}
		}
		if len(c.rules) > 0 {
			return 1
		}
		return 2
	}
	sort.Slice(ordered, func(i, j int) bool {
		a, b := ordered[i], ordered[j]
		if ra, rb := rank(a), rank(b); ra != rb {
			return ra < rb
		}
		if len(a.rules) > 0 && len(b.rules) > 0 && a.rules[0].key != b.rules[0].key {
			return before(a.rules[0], b.rules[0])
		}
		return a.name < b.name
	})
	encoded, err := json.Marshal(data)
	if err != nil {
		return "", fmt.Errorf("the page of the world cannot be written: %w", err)
	}
	start := ""
	if len(p.files) > 0 {
		start = p.files[0]
	}
	made := html.EscapeString(v.label("shows"))
	shown := html.EscapeString(v.label("shows_case"))
	var b strings.Builder
	b.WriteString("<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n")
	fmt.Fprintf(&b, "<title>%s</title>\n<style>\n%s</style>\n</head>\n<body>\n<main>\n<header>\n", html.EscapeString(start), pageStyle)
	fmt.Fprintf(&b, "<p class=\"origin\">%s</p>\n<h1>%s</h1>\n", html.EscapeString(start), v.atom(answer, false))
	if len(ordered) > 0 {
		b.WriteString("<nav>\n")
		for i, c := range ordered {
			fmt.Fprintf(&b, "<a href=\"#concept-%d\">%s</a>\n", i+1, html.EscapeString(c.title()))
		}
		b.WriteString("</nav>\n")
	}
	b.WriteString("</header>\n")
	for i, c := range ordered {
		fmt.Fprintf(&b, "<section class=\"concept\" id=\"concept-%d\">\n<h2>%s</h2>\n", i+1, html.EscapeString(c.title()))
		if !strings.EqualFold(c.title(), c.name) {
			fmt.Fprintf(&b, "<p class=\"name\"><code>%s</code></p>\n", html.EscapeString(c.name))
		}
		if len(c.rules) > 0 {
			fmt.Fprintf(&b, "<p class=\"label\">%s</p>\n<ul class=\"tree\">\n", made)
			for _, ref := range c.rules {
				fmt.Fprintf(&b, "<li><details class=\"rule\" data-rule=\"%s\"><summary>%s</summary></details></li>\n", html.EscapeString(ref.key), data.Rules[ref.key].Summary)
			}
			b.WriteString("</ul>\n")
		}
		if len(c.cases) > 0 {
			fmt.Fprintf(&b, "<p class=\"label\">%s</p>\n<ul class=\"cases\">\n", shown)
			for _, name := range c.cases {
				fmt.Fprintf(&b, "<li>%s</li>\n", html.EscapeString(name))
			}
			b.WriteString("</ul>\n")
		}
		b.WriteString("</section>\n")
	}
	fmt.Fprintf(&b, "</main>\n<script type=\"application/json\" id=\"universe-data\">%s</script>\n<script>\n%s</script>\n</body>\n</html>\n", encoded, pageScript)
	return b.String(), nil
}

const pageStyle = `:root {
  --bg: #f6f5f1;
  --card: #ffffff;
  --ink: #1f1e1b;
  --muted: #6c6a63;
  --line: #e2dfd6;
  --accent: #2b5983;
  --var: #9a4a2c;
  --code: #efede6;
  --again: #9a6c12;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #151514;
    --card: #1e1e1c;
    --ink: #ecebe6;
    --muted: #9d9b93;
    --line: #34332f;
    --accent: #8fb8de;
    --var: #e2a487;
    --code: #2a2926;
    --again: #d9ad55;
    color-scheme: dark;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink); font: 16px/1.55 ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
main { max-width: 54rem; margin: 0 auto; padding: 2.5rem 1rem 4rem; }
header { margin-bottom: 2rem; }
.origin { margin: 0; font: 0.85rem ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color: var(--muted); }
h1 { margin: 0.3rem 0 1.25rem; font-size: 2.1rem; line-height: 1.2; font-weight: 650; }
h1::first-letter { text-transform: uppercase; }
nav { display: flex; flex-wrap: wrap; gap: 0.4rem; }
nav a { color: var(--accent); text-decoration: none; background: var(--card); border: 1px solid var(--line); border-radius: 999px; padding: 0.15rem 0.7rem; font-size: 0.85rem; }
nav a:hover { border-color: var(--accent); }
.concept { background: var(--card); border: 1px solid var(--line); border-radius: 12px; padding: 1.25rem 1.25rem 1rem; margin: 0 0 1.25rem; scroll-margin-top: 1rem; }
h2 { margin: 0; font-size: 1.3rem; line-height: 1.3; }
.name { margin: 0.2rem 0 0; }
.name code { background: none; padding: 0; color: var(--muted); }
.label { margin: 1rem 0 0.3rem; font-size: 0.72rem; font-weight: 600; letter-spacing: 0.07em; text-transform: uppercase; color: var(--muted); }
.body > .label { margin-top: 0.55rem; }
ul.tree { list-style: none; margin: 0; padding: 0; }
.body { margin: 0.1rem 0 0.5rem 0.6rem; padding-left: 0.9rem; border-left: 2px solid var(--line); }
summary { display: flex; gap: 0.75rem; align-items: baseline; cursor: pointer; list-style: none; padding: 0.3rem 0.45rem; border-radius: 6px; }
summary::-webkit-details-marker { display: none; }
summary::before { content: "\25B8"; flex: none; color: var(--muted); transition: transform 0.15s; }
details[open] > summary::before { transform: rotate(90deg); }
summary:hover { background: var(--code); }
.leaf { padding: 0.3rem 0.45rem 0.3rem 1.6rem; }
.sentence { flex: 1; min-width: 0; }
.site { flex: none; font: 0.75rem ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color: var(--muted); }
.join { color: var(--muted); font-style: italic; }
var { font-style: italic; color: var(--var); }
var.any { color: var(--muted); }
.value { font-weight: 600; }
code { font: 0.85em ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; background: var(--code); border-radius: 4px; padding: 0.05rem 0.3rem; overflow-wrap: anywhere; }
code.word { color: var(--accent); }
.reading { color: var(--muted); }
.hole { display: inline-block; min-width: 1.2em; padding: 0 0.25em; border: 1px dashed var(--muted); border-radius: 4px; font-size: 0.75em; line-height: 1.35; text-align: center; }
pre.source { margin: 0.3rem 0 0.2rem; padding: 0.5rem 0.7rem; background: var(--code); border-radius: 6px; font: 0.8rem/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre-wrap; overflow-wrap: anywhere; }
.again > summary { color: var(--again); }
.again > summary::after { content: "\21BA"; flex: none; color: var(--again); }
ul.cases { display: flex; flex-wrap: wrap; gap: 0.4rem; list-style: none; margin: 0; padding: 0; }
ul.cases li { background: var(--code); border-radius: 6px; padding: 0.15rem 0.6rem; font-size: 0.9rem; }
@media (max-width: 36rem) {
  main { padding: 1.5rem 1rem 3rem; }
  h1 { font-size: 1.6rem; }
  .concept { padding: 1rem 0.85rem 0.75rem; }
  summary { flex-wrap: wrap; row-gap: 0.1rem; }
  .site { width: 100%; padding-left: 1.4rem; }
}
`

const pageScript = `(function () {
  var data = JSON.parse(document.getElementById("universe-data").textContent);
  function make(tag, className, markup) {
    var node = document.createElement(tag);
    if (className) node.className = className;
    if (markup) node.innerHTML = markup;
    return node;
  }
  function again(node, attribute, value) {
    for (var up = node.parentElement; up; up = up.parentElement) {
      if (up.getAttribute(attribute) === value) return true;
    }
    return false;
  }
  function ruleNode(key) {
    var details = make("details", "rule");
    details.setAttribute("data-rule", key);
    var summary = make("summary");
    if (data.rules[key]) summary.innerHTML = data.rules[key].summary;
    else summary.textContent = key;
    details.appendChild(summary);
    return details;
  }
  function wordNode(name) {
    var word = data.words[name];
    if (!word || word.rules.length === 0) {
      var leaf = make("div", "leaf");
      if (word) leaf.innerHTML = word.summary;
      else leaf.textContent = name;
      return leaf;
    }
    var details = make("details", "word");
    details.setAttribute("data-word", name);
    details.appendChild(make("summary", "", word.summary));
    return details;
  }
  function list(items, build) {
    var ul = make("ul", "tree");
    items.forEach(function (item) {
      var li = make("li");
      li.appendChild(build(item));
      ul.appendChild(li);
    });
    return ul;
  }
  function fill(details) {
    if (details.hasAttribute("data-filled")) return;
    details.setAttribute("data-filled", "");
    var body = make("div", "body");
    if (details.hasAttribute("data-rule")) {
      var key = details.getAttribute("data-rule");
      var rule = data.rules[key];
      if (again(details, "data-rule", key)) details.classList.add("again");
      if (rule && rule.source) {
        var pre = make("pre", "source");
        pre.textContent = rule.source;
        body.appendChild(pre);
      }
      if (rule && rule.words.length) {
        body.appendChild(make("p", "label", data.opens));
        body.appendChild(list(rule.words, wordNode));
      }
    } else {
      var name = details.getAttribute("data-word");
      var word = data.words[name];
      if (again(details, "data-word", name)) details.classList.add("again");
      body.appendChild(make("p", "label", data.explained));
      body.appendChild(list(word ? word.rules : [], ruleNode));
    }
    details.appendChild(body);
  }
  document.addEventListener("toggle", function (event) {
    var target = event.target;
    if (target instanceof HTMLDetailsElement && target.open) fill(target);
  }, true);
})();
`
