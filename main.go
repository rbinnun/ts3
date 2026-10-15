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
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/parse/gen"
	"github.com/antlr4-go/antlr/v4"
	"mvdan.cc/sh/v3/fileutil"
	"mvdan.cc/sh/v3/syntax"
)

const mangleModule = "codeberg.org/TauCeti/mangle-go"

var (
	doesSym       = ast.PredicateSym{Symbol: "does", Arity: 1}
	effectSym     = ast.PredicateSym{Symbol: "effect", Arity: 2}
	givesSym      = ast.PredicateSym{Symbol: "gives", Arity: 3}
	gotSym        = ast.PredicateSym{Symbol: "got", Arity: 3}
	machineSym    = ast.PredicateSym{Symbol: "machine_program", Arity: 1}
	tellsName     = "tells"
	violationName = "violation"
	stepNames     = map[string]bool{"does": true, "effect": true, "gives": true, "got": true}
	outcomeNames  = map[string]bool{"does": true, "effect": true, "gives": true, "got": true, "tells": true, "violation": true}
)

const maxRounds = 100

type machine struct {
	dir      string
	entry    string
	program  string
	programs []string
	without  map[string][]byte
	nested   bool
	shared   *shared
}

type shared struct {
	measured bool
	baseline map[string]meaning
	err      error
}

func (m *machine) at(path string) string {
	if filepath.IsAbs(path) {
		return filepath.Clean(path)
	}
	return filepath.Join(m.dir, path)
}

func (m *machine) aside(without map[string][]byte) *machine {
	return &machine{dir: m.dir, entry: m.entry, program: m.program, without: without, nested: true, shared: m.shared}
}

func (m *machine) source(path string) ([]byte, error) {
	if src, ok := m.without[filepath.Clean(path)]; ok {
		return src, nil
	}
	return os.ReadFile(path)
}

type effectFunc func(m *machine, in map[string][]ast.Constant) ([]result, error)

type effectKind struct {
	do    effectFunc
	gives []string
}

type result struct {
	field string
	value ast.Constant
}

var effects map[string]effectKind

func init() {
	effects = map[string]effectKind{
		"list_a_folder":    {listAFolder, []string{"file"}},
		"find_comments":    {findComments, []string{"syntax", "comment"}},
		"read_lines":       {readLines, []string{"line"}},
		"know_the_machine": {knowTheMachine, []string{"mangle_module", "mangle_version", "entry_point", "machine_program"}},
		"take_out_a_line":  {takeOutALine, []string{"changed"}},
	}
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
		os.Exit(2)
	}
	if err := run(flag.Arg(0), *entry); err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(1)
	}
}

type evaluator func(got []ast.Atom) (factstore.FactStore, error)

func (m *machine) parseFile(path string) (parse.SourceUnit, error) {
	src, err := m.source(path)
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

type outcome struct {
	store factstore.FactStore
	eval  evaluator
	got   []ast.Atom
}

func run(path, entry string) error {
	m := &machine{dir: filepath.Dir(path), entry: entry, program: filepath.Clean(path), shared: &shared{}}
	o, err := execute(m)
	if err != nil {
		return err
	}
	if violations := lines(o.store, violationName); len(violations) > 0 {
		for _, v := range violations {
			fmt.Fprintln(os.Stderr, "violation:", v)
		}
		return fmt.Errorf("%s does not hold: %d violation(s)", filepath.Base(path), len(violations))
	}
	for _, l := range lines(o.store, tellsName) {
		fmt.Println(l)
	}
	return nil
}

func execute(m *machine) (*outcome, error) {
	unit, err := m.parseFile(m.program)
	if err != nil {
		return nil, err
	}
	names := []string{m.program}
	units := []parse.SourceUnit{unit}
	eval, err := compile(names, units)
	if err != nil {
		return nil, err
	}
	store, err := eval(nil)
	if err != nil {
		return nil, err
	}

	var wanted []string
	for _, f := range facts(store, machineSym) {
		wanted = append(wanted, str(f[0]))
	}
	sort.Strings(wanted)
	m.programs = nil
	for _, name := range wanted {
		unit, err := m.parseFile(m.at(name))
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
		if store, err = eval(nil); err != nil {
			return nil, err
		}
	}

	if err := checkHow(store, m.entry); err != nil {
		return nil, err
	}

	var got []ast.Atom
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
	return &outcome{store: store, eval: eval, got: got}, nil
}

func lines(store factstore.FactStore, name string) []string {
	var out []string
	for _, pred := range store.ListPredicates() {
		if pred.Symbol != name {
			continue
		}
		for _, args := range facts(store, pred) {
			parts := make([]string, len(args))
			for i, a := range args {
				parts[i] = show(a)
			}
			out = append(out, strings.Join(parts, "\t"))
		}
	}
	sort.Strings(out)
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

func checkHow(store factstore.FactStore, entry string) error {
	linked := linkedVersion()
	for _, f := range facts(store, ast.PredicateSym{Symbol: "mangle_module", Arity: 1}) {
		if want := str(f[0]); want != mangleModule {
			return fmt.Errorf("program wants Mangle module %q, this runner is built on %q", want, mangleModule)
		}
	}
	for _, f := range facts(store, ast.PredicateSym{Symbol: "mangle_version", Arity: 1}) {
		if want := str(f[0]); want != linked {
			return fmt.Errorf("program wants Mangle %s, this runner is built on %q", want, linked)
		}
	}
	if entry != "" {
		for _, f := range facts(store, ast.PredicateSym{Symbol: "entry_point", Arity: 1}) {
			if want := str(f[0]); want != entry {
				return fmt.Errorf("program's entry point is %q, but it was started through %q", want, entry)
			}
		}
	}
	return nil
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
	kind, ok := effects[kinds[0]]
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
	return kind.do(m, in)
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
	at := m.at(path)
	src, err := os.ReadFile(at)
	if err != nil {
		return nil, err
	}
	var comments []string
	var lang string
	switch filepath.Ext(path) {
	case ".mg":
		lang = "mangle"
		comments, err = mangleComments(src)
	case ".go":
		lang = "go"
		comments, err = goComments(at, src)
	default:
		lang, comments, err = shellComments(at, src)
	}
	if err != nil {
		return nil, fmt.Errorf("find_comments in %s: %w", path, err)
	}
	out := []result{{"syntax", ast.String(lang)}}
	for _, c := range comments {
		out = append(out, result{"comment", ast.String(c)})
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
	out := []result{{"mangle_module", ast.String(mangleModule)}}
	if v := linkedVersion(); v != "" {
		out = append(out, result{"mangle_version", ast.String(v)})
	}
	if m.entry != "" {
		out = append(out, result{"entry_point", ast.String(m.entry)})
	}
	for _, p := range m.programs {
		out = append(out, result{"machine_program", ast.String(p)})
	}
	return out, nil
}

func takeOutALine(m *machine, in map[string][]ast.Constant) ([]result, error) {
	path, err := onlyString("take_out_a_line", "path", in)
	if err != nil {
		return nil, err
	}
	line, err := onlyString("take_out_a_line", "line", in)
	if err != nil {
		return nil, err
	}
	if m.nested {
		return nil, nil
	}
	at := m.at(path)
	src, err := m.source(at)
	if err != nil {
		return nil, err
	}
	rest, ok := takeOut(src, line)
	if !ok {
		return nil, fmt.Errorf("take_out_a_line: %s has no line %q", path, line)
	}
	before, err := m.shared.baselineOf(m)
	if err != nil {
		return nil, fmt.Errorf("take_out_a_line: %s with every line in it: %w", path, err)
	}
	var after map[string]meaning
	if o, err := execute(m.aside(map[string][]byte{at: rest})); err == nil {
		after = meanings(o)
	}
	var out []result
	for _, doing := range changed(before, after) {
		out = append(out, result{"changed", doing})
	}
	return out, nil
}

func takeOut(src []byte, line string) ([]byte, bool) {
	all := strings.SplitAfter(string(src), "\n")
	for i, l := range all {
		if strings.TrimSuffix(strings.TrimSuffix(l, "\n"), "\r") == line {
			return []byte(strings.Join(append(all[:i:i], all[i+1:]...), "")), true
		}
	}
	return nil, false
}

func (s *shared) baselineOf(m *machine) (map[string]meaning, error) {
	if !s.measured {
		s.measured = true
		o, err := execute(m.aside(nil))
		if err != nil {
			s.err = err
		} else {
			s.baseline = meanings(o)
		}
	}
	return s.baseline, s.err
}

type meaning struct {
	doing ast.Constant
	text  string
}

func meanings(o *outcome) map[string]meaning {
	actual := outcomeOf(o.store)
	out := map[string]meaning{}
	for _, d := range facts(o.store, doesSym) {
		doing := d[0]
		var b strings.Builder
		b.WriteString("step\n")
		for _, key := range sortedKeys(actual) {
			a := actual[key]
			if stepNames[a.Predicate.Symbol] && len(a.Args) > 0 && a.Args[0].Equals(doing) {
				b.WriteString(key + "\n")
			}
		}
		var rest []ast.Atom
		for _, g := range o.got {
			if !g.Args[0].Equals(doing) {
				rest = append(rest, g)
			}
		}
		b.WriteString("given nothing\n")
		if len(rest) != len(o.got) {
			b.WriteString(probe(o, actual, rest))
		}
		kinds := effectsOf(o.store, doing)
		if len(kinds) == 1 {
			for _, field := range effects[kinds[0]].gives {
				more := append(append([]ast.Atom(nil), o.got...), ast.NewAtom(gotSym.Symbol, doing, ast.String(field), unexpected(o.got, doing, field)))
				b.WriteString("given an unexpected " + field + "\n")
				b.WriteString(probe(o, actual, more))
			}
		}
		out[doing.String()] = meaning{doing: doing, text: b.String()}
	}
	return out
}

func probe(o *outcome, actual map[string]ast.Atom, got []ast.Atom) string {
	store, err := o.eval(got)
	if err != nil {
		return "fails: " + err.Error() + "\n"
	}
	then := outcomeOf(store)
	var diff []string
	for key := range then {
		if _, ok := actual[key]; !ok {
			diff = append(diff, "+ "+key)
		}
	}
	for key := range actual {
		if _, ok := then[key]; !ok {
			diff = append(diff, "- "+key)
		}
	}
	sort.Strings(diff)
	var b strings.Builder
	for _, d := range diff {
		b.WriteString(d + "\n")
	}
	return b.String()
}

func unexpected(got []ast.Atom, doing ast.Constant, field string) ast.Constant {
	value := "unexpected"
	for taken := true; taken; {
		taken = false
		for _, g := range got {
			if g.Args[0].Equals(doing) && g.Args[1].Equals(ast.String(field)) && g.Args[2].Equals(ast.String(value)) {
				taken = true
				value += "!"
				break
			}
		}
	}
	return ast.String(value)
}

func outcomeOf(store factstore.FactStore) map[string]ast.Atom {
	out := map[string]ast.Atom{}
	for _, pred := range store.ListPredicates() {
		if !outcomeNames[pred.Symbol] {
			continue
		}
		store.GetFacts(ast.NewQuery(pred), func(a ast.Atom) error {
			out[a.String()] = a
			return nil
		})
	}
	return out
}

func sortedKeys(m map[string]ast.Atom) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func changed(before, after map[string]meaning) []ast.Constant {
	seen := map[string]bool{}
	var keys []string
	for _, side := range []map[string]meaning{before, after} {
		for k := range side {
			if !seen[k] {
				seen[k] = true
				keys = append(keys, k)
			}
		}
	}
	sort.Strings(keys)
	var out []ast.Constant
	for _, k := range keys {
		b, inBefore := before[k]
		a, inAfter := after[k]
		switch {
		case inBefore && inAfter && a.text == b.text:
		case inBefore:
			out = append(out, b.doing)
		default:
			out = append(out, a.doing)
		}
	}
	return out
}

type lexErrors struct {
	*antlr.DefaultErrorListener
	errs []string
}

func (l *lexErrors) SyntaxError(_ antlr.Recognizer, _ any, line, column int, msg string, _ antlr.RecognitionException) {
	l.errs = append(l.errs, fmt.Sprintf("%d:%d: %s", line, column, msg))
}

func mangleComments(src []byte) ([]string, error) {
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

func shellComments(name string, src []byte) (string, []string, error) {
	lang := syntax.LangPOSIX
	if bytes.HasPrefix(src, []byte("#!")) {
		shell := fileutil.Shebang(src)
		if shell == "" {
			return "", nil, errors.New("starts with #! but names no shell whose comments are known")
		}
		if err := lang.Set(shell); err != nil {
			return "", nil, err
		}
	}
	f, err := syntax.NewParser(syntax.KeepComments(true), syntax.Variant(lang)).Parse(bytes.NewReader(src), name)
	if err != nil {
		return "", nil, err
	}
	var out []string
	syntax.Walk(f, func(n syntax.Node) bool {
		if c, ok := n.(*syntax.Comment); ok {
			out = append(out, "#"+c.Text)
		}
		return true
	})
	return lang.String(), out, nil
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
