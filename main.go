package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"go/scanner"
	"go/token"
	"os"
	"path/filepath"
	"runtime/debug"
	"slices"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/parse/gen"
	"github.com/antlr4-go/antlr/v4"
	"mvdan.cc/sh/v3/syntax"
)

const mangleModule = "codeberg.org/TauCeti/mangle-go"

var (
	doesSym     = ast.PredicateSym{Symbol: "does", Arity: 1}
	effectSym   = ast.PredicateSym{Symbol: "effect", Arity: 2}
	givesSym    = ast.PredicateSym{Symbol: "gives", Arity: 3}
	gotSym      = ast.PredicateSym{Symbol: "got", Arity: 3}
	machineSym  = ast.PredicateSym{Symbol: "machine_program", Arity: 1}
	outputSym   = ast.PredicateSym{Symbol: "output", Arity: 2}
	answerSym   = ast.PredicateSym{Symbol: "answer", Arity: 1}
	exitCodeSym = ast.PredicateSym{Symbol: "exit_code", Arity: 2}
	startedSym  = ast.PredicateSym{Symbol: "started_by", Arity: 1}
)

const (
	maxRounds  = 100
	brokenExit = 2
	runACaseFx = "run_a_case"
)

type machine struct {
	dir       string
	program   string
	entry     string
	startedBy []string
	programs  []string
}

type outcome struct {
	code int
	told []ast.Atom
}

func (m *machine) at(path string) string {
	if filepath.IsAbs(path) {
		return filepath.Clean(path)
	}
	return filepath.Join(m.dir, path)
}

type effectFunc func(m *machine, in map[string][]ast.Constant) ([]result, error)

type result struct {
	field string
	value ast.Constant
}

var effects map[string]effectFunc

func init() {
	effects = map[string]effectFunc{
		"list_a_folder":    listAFolder,
		"find_comments":    findComments,
		"read_a_program":   readAProgram,
		"read_lines":       readLines,
		"know_the_machine": knowTheMachine,
		runACaseFx:         runACase,
	}
}

var commentFinders = map[string]func(name string, src []byte) ([]string, error){
	"mangle": mangleComments,
	"go":     goComments,
	"sh":     shellComments,
}

func main() {
	entry := flag.String("entry", "", "name of the entry point this runner was started through")
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: %s [-entry NAME] PROGRAM.mg\n", filepath.Base(os.Args[0]))
		flag.PrintDefaults()
	}
	flag.Parse()
	if flag.NArg() != 1 {
		flag.Usage()
		os.Exit(brokenExit)
	}
	code, err := run(flag.Arg(0), *entry)
	if err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(brokenExit)
	}
	os.Exit(code)
}

type evaluator func(got []ast.Atom) (factstore.FactStore, error)

func parseFile(path string) (parse.SourceUnit, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return parse.SourceUnit{}, err
	}
	unit, err := parse.Unit(bytes.NewReader(src))
	if err != nil {
		return parse.SourceUnit{}, fmt.Errorf("parsing %s: %w", path, err)
	}
	return unit, nil
}

func compile(names []string, units []parse.SourceUnit) (evaluator, error) {
	what := strings.Join(names, " with ")
	info, err := analysis.Analyze(units, nil)
	if err != nil {
		return nil, fmt.Errorf("analyzing %s: %w", what, err)
	}
	strata, predToStratum, err := analysis.Stratify(analysis.Program{
		EdbPredicates: info.EdbPredicates,
		IdbPredicates: info.IdbPredicates,
		Rules:         info.Rules,
	})
	if err != nil {
		return nil, fmt.Errorf("stratifying %s: %w", what, err)
	}
	return func(got []ast.Atom) (factstore.FactStore, error) {
		store := factstore.NewSimpleInMemoryStore()
		for _, g := range got {
			store.Add(g)
		}
		_, err := engine.EvalStratifiedProgramWithStats(info, strata, predToStratum, store)
		return store, err
	}, nil
}

func run(path, entry string) (int, error) {
	m := &machine{entry: entry}
	o, err := m.outcome(path)
	if err != nil {
		return 0, err
	}
	var out []string
	for _, a := range o.told {
		out = append(out, a.String()+".")
	}
	sort.Strings(out)
	for _, l := range out {
		fmt.Println(l)
	}
	return o.code, nil
}

func (m *machine) outcome(path string) (outcome, error) {
	program := filepath.Clean(path)
	m.dir, m.program = filepath.Dir(program), filepath.Base(program)
	store, err := m.execute(program)
	if err != nil {
		return outcome{}, err
	}
	var told []ast.Atom
	for _, o := range facts(store, outputSym) {
		if format := str(o[1]); format != "mangle" {
			return outcome{}, fmt.Errorf("cannot write %s in %q", str(o[0]), format)
		}
		told = append(told, factsNamed(store, str(o[0]))...)
	}
	code, err := exitCode(store)
	if err != nil {
		return outcome{}, err
	}
	return outcome{code: code, told: told}, nil
}

func (m *machine) given() []ast.Atom {
	var out []ast.Atom
	for _, s := range m.startedBy {
		out = append(out, ast.NewAtom(startedSym.Symbol, ast.String(s)))
	}
	return out
}

func exitCode(store factstore.FactStore) (int, error) {
	answers := facts(store, answerSym)
	if len(answers) != 1 {
		return 0, fmt.Errorf("needs exactly one answer, found %d", len(answers))
	}
	var codes []ast.Constant
	for _, e := range facts(store, exitCodeSym) {
		if e[0].Equals(answers[0][0]) {
			codes = append(codes, e[1])
		}
	}
	if len(codes) != 1 {
		return 0, fmt.Errorf("answer %s needs exactly one exit code, found %d", show(answers[0][0]), len(codes))
	}
	code, err := codes[0].NumberValue()
	if err != nil || code < 0 || code > 255 {
		return 0, fmt.Errorf("answer %s has exit code %v, not a number from 0 to 255", show(answers[0][0]), codes[0])
	}
	return int(code), nil
}

func (m *machine) execute(program string) (factstore.FactStore, error) {
	unit, err := parseFile(program)
	if err != nil {
		return nil, err
	}
	names := []string{program}
	units := []parse.SourceUnit{unit}
	eval, err := compile(names, units)
	if err != nil {
		return nil, err
	}
	store, err := eval(m.given())
	if err != nil {
		return nil, err
	}

	var wanted []string
	for _, f := range facts(store, machineSym) {
		wanted = append(wanted, str(f[0]))
	}
	sort.Strings(wanted)
	for _, name := range wanted {
		unit, err := parseFile(m.at(name))
		if errors.Is(err, os.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, err
		}
		names = append(names, m.at(name))
		units = append(units, unit)
		m.programs = append(m.programs, name)
	}
	if len(m.programs) > 0 {
		if eval, err = compile(names, units); err != nil {
			return nil, err
		}
		if store, err = eval(m.given()); err != nil {
			return nil, err
		}
	}

	got := m.given()
	done := map[string]bool{}
	for round := 0; ; round++ {
		if round == maxRounds {
			return nil, fmt.Errorf("still asking for new effects after %d rounds", maxRounds)
		}
		var todo []ast.Constant
		for _, d := range facts(store, doesSym) {
			if !done[d[0].String()] {
				todo = append(todo, d[0])
			}
		}
		if len(todo) == 0 {
			break
		}
		sort.Slice(todo, func(i, j int) bool { return todo[i].String() < todo[j].String() })
		for _, doing := range todo {
			done[doing.String()] = true
			out, err := perform(store, m, doing)
			if err != nil {
				return nil, fmt.Errorf("does(%v): %w", doing, err)
			}
			for _, r := range out {
				got = append(got, ast.NewAtom(gotSym.Symbol, doing, ast.String(r.field), r.value))
			}
		}
		if store, err = eval(got); err != nil {
			return nil, err
		}
	}
	return store, nil
}

func factsNamed(store factstore.FactStore, name string) []ast.Atom {
	var out []ast.Atom
	for _, pred := range store.ListPredicates() {
		if pred.Symbol != name {
			continue
		}
		store.GetFacts(ast.NewQuery(pred), func(a ast.Atom) error {
			out = append(out, a)
			return nil
		})
	}
	return out
}

func linkedVersion() string {
	linked := ""
	if bi, ok := debug.ReadBuildInfo(); ok {
		for _, dep := range bi.Deps {
			if dep.Path == mangleModule {
				linked = dep.Version
				if dep.Replace != nil {
					linked = dep.Replace.Version
				}
			}
		}
	}
	return linked
}

func effectsOf(store factstore.FactStore, doing ast.Constant) []string {
	var kinds []string
	for _, e := range facts(store, effectSym) {
		if e[0].Equals(doing) {
			kinds = append(kinds, str(e[1]))
		}
	}
	return kinds
}

func perform(store factstore.FactStore, m *machine, doing ast.Constant) ([]result, error) {
	kinds := effectsOf(store, doing)
	if len(kinds) != 1 {
		return nil, fmt.Errorf("needs exactly one effect, found %d %v", len(kinds), kinds)
	}
	do, ok := effects[kinds[0]]
	if !ok {
		known := make([]string, 0, len(effects))
		for k := range effects {
			known = append(known, k)
		}
		sort.Strings(known)
		return nil, fmt.Errorf("unknown effect %q (known: %s)", kinds[0], strings.Join(known, ", "))
	}
	in := map[string][]ast.Constant{}
	for _, g := range facts(store, givesSym) {
		if g[0].Equals(doing) {
			field := str(g[1])
			in[field] = append(in[field], g[2])
		}
	}
	return do(m, in)
}

func onlyString(effect, field string, in map[string][]ast.Constant) (string, error) {
	values := in[field]
	if len(values) != 1 {
		return "", fmt.Errorf("%s needs exactly one %q, got %d", effect, field, len(values))
	}
	s, err := values[0].StringValue()
	if err != nil {
		return "", fmt.Errorf("%s: %s must be a string: %w", effect, field, err)
	}
	return s, nil
}

func listAFolder(m *machine, in map[string][]ast.Constant) ([]result, error) {
	folder, err := onlyString("list_a_folder", "folder", in)
	if err != nil {
		return nil, err
	}
	at := m.at(folder)
	entries, err := os.ReadDir(at)
	if err != nil {
		return nil, err
	}
	var out []result
	for _, e := range entries {
		fi, err := os.Stat(filepath.Join(at, e.Name()))
		if err != nil {
			if errors.Is(err, os.ErrNotExist) {
				continue
			}
			return nil, err
		}
		if fi.IsDir() {
			continue
		}
		out = append(out, result{"file", ast.String(filepath.Join(folder, e.Name()))})
	}
	return out, nil
}

func findComments(m *machine, in map[string][]ast.Constant) ([]result, error) {
	path, err := onlyString("find_comments", "path", in)
	if err != nil {
		return nil, err
	}
	lang, err := onlyString("find_comments", "language", in)
	if err != nil {
		return nil, err
	}
	find, ok := commentFinders[lang]
	if !ok {
		return nil, fmt.Errorf("find_comments knows no comments in %q", lang)
	}
	at := m.at(path)
	src, err := os.ReadFile(at)
	if err != nil {
		return nil, err
	}
	comments, err := find(at, src)
	if err != nil {
		return nil, fmt.Errorf("find_comments in %s: %w", path, err)
	}
	out := []result{{"syntax", ast.String(lang)}}
	for _, c := range comments {
		out = append(out, result{"comment", ast.String(c)})
	}
	return out, nil
}

func readAProgram(m *machine, in map[string][]ast.Constant) ([]result, error) {
	path, err := onlyString("read_a_program", "path", in)
	if err != nil {
		return nil, err
	}
	unit, err := parseFile(m.at(path))
	if err != nil {
		return nil, err
	}
	lawsIn := map[string]bool{}
	for _, c := range in["laws_in"] {
		lawsIn[str(c)] = true
	}
	var out []result
	seen := map[string]bool{}
	for _, c := range unit.Clauses {
		name := c.Head.Predicate.Symbol
		if !seen["defines\x00"+name] {
			seen["defines\x00"+name] = true
			out = append(out, result{"defines", ast.String(name)})
		}
		if !lawsIn[name] || len(c.Head.Args) == 0 {
			continue
		}
		law, ok := c.Head.Args[0].(ast.Constant)
		if !ok || seen["law\x00"+law.String()] {
			continue
		}
		seen["law\x00"+law.String()] = true
		out = append(out, result{"law", law})
	}
	return out, nil
}

func readLines(m *machine, in map[string][]ast.Constant) ([]result, error) {
	path, err := onlyString("read_lines", "path", in)
	if err != nil {
		return nil, err
	}
	src, err := os.ReadFile(m.at(path))
	if err != nil {
		return nil, err
	}
	if len(src) == 0 {
		return nil, nil
	}
	var out []result
	for _, line := range strings.Split(strings.TrimSuffix(string(src), "\n"), "\n") {
		out = append(out, result{"line", ast.String(strings.TrimSuffix(line, "\r"))})
	}
	return out, nil
}

func knowTheMachine(m *machine, in map[string][]ast.Constant) ([]result, error) {
	out := []result{
		{"mangle_module", ast.String(mangleModule)},
		{"exits_broken_with", ast.Number(brokenExit)},
	}
	if v := linkedVersion(); v != "" {
		out = append(out, result{"mangle_version", ast.String(v)})
	}
	if m.entry != "" {
		out = append(out, result{"entry_point", ast.String(m.entry)})
	}
	for _, p := range m.programs {
		out = append(out, result{"machine_program", ast.String(p)})
	}
	for _, s := range m.startedBy {
		out = append(out, result{"started_by", ast.String(s)})
	}
	return out, nil
}

func runACase(m *machine, in map[string][]ast.Constant) ([]result, error) {
	if slices.Contains(m.startedBy, runACaseFx) {
		return nil, fmt.Errorf("%s cannot start inside a case", runACaseFx)
	}
	tmp, err := os.MkdirTemp("", "universe-case-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(tmp)
	if err := m.copyFolder(tmp); err != nil {
		return nil, err
	}
	paths := make([]string, 0, len(in))
	for p := range in {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	for _, p := range paths {
		if !filepath.IsLocal(p) {
			return nil, fmt.Errorf("%s cannot add lines to %q, which is outside the folder", runACaseFx, p)
		}
		var lines []string
		for _, c := range in[p] {
			line, err := c.StringValue()
			if err != nil {
				return nil, fmt.Errorf("%s: a line for %s must be a string: %w", runACaseFx, p, err)
			}
			lines = append(lines, line)
		}
		sort.Strings(lines)
		if err := addLines(filepath.Join(tmp, p), lines); err != nil {
			return nil, err
		}
	}
	inner := &machine{entry: m.entry, startedBy: append(slices.Clone(m.startedBy), runACaseFx)}
	o, err := inner.outcome(filepath.Join(tmp, m.program))
	if err != nil {
		return []result{{"exit", ast.Number(brokenExit)}}, nil
	}
	out := []result{{"exit", ast.Number(int64(o.code))}}
	seen := map[string]bool{}
	for _, a := range o.told {
		if len(a.Args) == 0 {
			continue
		}
		c, ok := a.Args[0].(ast.Constant)
		if !ok {
			continue
		}
		key := a.Predicate.Symbol + "\x00" + c.String()
		if seen[key] {
			continue
		}
		seen[key] = true
		out = append(out, result{a.Predicate.Symbol, c})
	}
	return out, nil
}

func (m *machine) copyFolder(to string) error {
	entries, err := os.ReadDir(m.dir)
	if err != nil {
		return err
	}
	for _, e := range entries {
		from := filepath.Join(m.dir, e.Name())
		fi, err := os.Stat(from)
		if err != nil {
			if errors.Is(err, os.ErrNotExist) {
				continue
			}
			return err
		}
		if !fi.Mode().IsRegular() {
			continue
		}
		src, err := os.ReadFile(from)
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(to, e.Name()), src, fi.Mode().Perm()); err != nil {
			return err
		}
	}
	return nil
}

func addLines(path string, lines []string) error {
	src, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	if len(src) > 0 && !bytes.HasSuffix(src, []byte("\n")) {
		src = append(src, '\n')
	}
	for _, l := range lines {
		src = append(append(src, l...), '\n')
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, src, 0o644)
}

type lexErrors struct {
	*antlr.DefaultErrorListener
	errs []string
}

func (l *lexErrors) SyntaxError(_ antlr.Recognizer, _ any, line, column int, msg string, _ antlr.RecognitionException) {
	l.errs = append(l.errs, fmt.Sprintf("%d:%d: %s", line, column, msg))
}

func mangleComments(_ string, src []byte) ([]string, error) {
	lexer := gen.NewMangleLexer(antlr.NewInputStream(string(src)))
	lexer.RemoveErrorListeners()
	errs := &lexErrors{DefaultErrorListener: antlr.NewDefaultErrorListener()}
	lexer.AddErrorListener(errs)
	var out []string
	for tok := lexer.NextToken(); tok.GetTokenType() != antlr.TokenEOF; tok = lexer.NextToken() {
		if tok.GetTokenType() == gen.MangleLexerCOMMENT {
			out = append(out, tok.GetText())
		}
	}
	if len(errs.errs) > 0 {
		return nil, errors.New(strings.Join(errs.errs, "; "))
	}
	return out, nil
}

func goComments(name string, src []byte) ([]string, error) {
	fset := token.NewFileSet()
	var errs scanner.ErrorList
	var s scanner.Scanner
	s.Init(fset.AddFile(name, -1, len(src)), src, errs.Add, scanner.ScanComments)
	var out []string
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			break
		}
		if tok == token.COMMENT {
			out = append(out, lit)
		}
	}
	if err := errs.Err(); err != nil {
		return nil, err
	}
	return out, nil
}

func shellComments(name string, src []byte) ([]string, error) {
	f, err := syntax.NewParser(syntax.KeepComments(true), syntax.Variant(syntax.LangPOSIX)).Parse(bytes.NewReader(src), name)
	if err != nil {
		return nil, err
	}
	var out []string
	syntax.Walk(f, func(n syntax.Node) bool {
		if c, ok := n.(*syntax.Comment); ok {
			out = append(out, "#"+c.Text)
		}
		return true
	})
	return out, nil
}

func facts(store factstore.FactStore, pred ast.PredicateSym) [][]ast.Constant {
	var out [][]ast.Constant
	store.GetFacts(ast.NewQuery(pred), func(a ast.Atom) error {
		args := make([]ast.Constant, len(a.Args))
		for i, t := range a.Args {
			args[i], _ = t.(ast.Constant)
		}
		out = append(out, args)
		return nil
	})
	return out
}

func str(c ast.Constant) string {
	if s, err := c.StringValue(); err == nil {
		return s
	}
	return c.Symbol
}

func show(c ast.Constant) string {
	if c.Type == ast.StringType {
		return c.Symbol
	}
	return c.String()
}
