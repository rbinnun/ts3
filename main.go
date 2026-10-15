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
	tellsName     = "tells"
	violationName = "violation"
)

const maxRounds = 100

type effectFunc func(dir string, in map[string][]ast.Constant) ([]result, error)

type result struct {
	field string
	value ast.Constant
}

var effects = map[string]effectFunc{
	"list_a_folder": listAFolder,
	"find_comments": findComments,
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

func run(path, entry string) error {
	src, err := os.Open(path)
	if err != nil {
		return err
	}
	unit, err := parse.Unit(src)
	src.Close()
	if err != nil {
		return fmt.Errorf("parsing %s: %w", path, err)
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		return fmt.Errorf("analyzing %s: %w", path, err)
	}
	strata, predToStratum, err := analysis.Stratify(analysis.Program{
		EdbPredicates: info.EdbPredicates,
		IdbPredicates: info.IdbPredicates,
		Rules:         info.Rules,
	})
	if err != nil {
		return fmt.Errorf("stratifying %s: %w", path, err)
	}
	eval := func(got []ast.Atom) (factstore.FactStore, error) {
		store := factstore.NewSimpleInMemoryStore()
		for _, g := range got {
			store.Add(g)
		}
		_, err := engine.EvalStratifiedProgramWithStats(info, strata, predToStratum, store)
		return store, err
	}

	dir := filepath.Dir(path)
	var got []ast.Atom
	done := map[string]bool{}
	store, err := eval(nil)
	if err != nil {
		return err
	}
	if err := checkHow(store, entry); err != nil {
		return err
	}

	for round := 0; ; round++ {
		if round == maxRounds {
			return fmt.Errorf("still asking for new effects after %d rounds", maxRounds)
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
		for _, doing := range todo {
			done[doing.String()] = true
			out, err := perform(store, dir, doing)
			if err != nil {
				return fmt.Errorf("does(%v): %w", doing, err)
			}
			for _, r := range out {
				got = append(got, ast.NewAtom(gotSym.Symbol, doing, ast.String(r.field), r.value))
			}
		}
		if store, err = eval(got); err != nil {
			return err
		}
	}

	if violations := lines(store, violationName); len(violations) > 0 {
		for _, v := range violations {
			fmt.Fprintln(os.Stderr, "violation:", v)
		}
		return fmt.Errorf("%s does not hold: %d violation(s)", filepath.Base(path), len(violations))
	}
	for _, l := range lines(store, tellsName) {
		fmt.Println(l)
	}
	return nil
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

func checkHow(store factstore.FactStore, entry string) error {
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

func perform(store factstore.FactStore, dir string, doing ast.Constant) ([]result, error) {
	var kinds []string
	for _, e := range facts(store, effectSym) {
		if e[0].Equals(doing) {
			kinds = append(kinds, str(e[1]))
		}
	}
	if len(kinds) != 1 {
		return nil, fmt.Errorf("needs exactly one effect, found %d %v", len(kinds), kinds)
	}
	fn, ok := effects[kinds[0]]
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
	return fn(dir, in)
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

func listAFolder(dir string, in map[string][]ast.Constant) ([]result, error) {
	folder, err := onlyString("list_a_folder", "folder", in)
	if err != nil {
		return nil, err
	}
	at := folder
	if !filepath.IsAbs(at) {
		at = filepath.Join(dir, folder)
	}
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

func findComments(dir string, in map[string][]ast.Constant) ([]result, error) {
	path, err := onlyString("find_comments", "path", in)
	if err != nil {
		return nil, err
	}
	at := path
	if !filepath.IsAbs(at) {
		at = filepath.Join(dir, path)
	}
	src, err := os.ReadFile(at)
	if err != nil {
		return nil, err
	}
	var comments []string
	switch filepath.Ext(path) {
	case ".mg":
		comments, err = mangleComments(src)
	case ".go":
		comments, err = goComments(at, src)
	default:
		comments, err = shellComments(at, src)
	}
	if err != nil {
		return nil, fmt.Errorf("find_comments in %s: %w", path, err)
	}
	out := make([]result, len(comments))
	for i, c := range comments {
		out[i] = result{"comment", ast.String(c)}
	}
	return out, nil
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

func shellComments(name string, src []byte) ([]string, error) {
	lang := syntax.LangPOSIX
	if bytes.HasPrefix(src, []byte("#!")) {
		shell := fileutil.Shebang(src)
		if shell == "" {
			return nil, errors.New("starts with #! but names no shell whose comments are known")
		}
		if err := lang.Set(shell); err != nil {
			return nil, err
		}
	}
	f, err := syntax.NewParser(syntax.KeepComments(true), syntax.Variant(lang)).Parse(bytes.NewReader(src), name)
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
