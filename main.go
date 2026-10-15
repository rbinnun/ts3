// Command universe runs a Mangle program that asks the world for things.
//
// The program talks to this runner through a few predicates:
//
//	does(Doing).                  something the program wants done
//	effect(Doing, Kind).          which kind of effect does it
//	gives(Doing, Field, Value).   the inputs it hands to that effect
//	got(Doing, Field, Value).     what the effect gave back (filled in here)
//	tells(...).                   what the program says once it knows
//
// and three facts about how it should be run:
//
//	mangle_module(Path).  mangle_version(Version).  entry_point(File).
//
// The runner evaluates the program, performs every effect the program asks
// for, adds the results as got/3 facts, evaluates again until nothing new is
// asked, and then prints every tells fact, one per line.
package main

import (
	"errors"
	"flag"
	"fmt"
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
)

const mangleModule = "codeberg.org/TauCeti/mangle-go"

var (
	doesSym   = ast.PredicateSym{Symbol: "does", Arity: 1}
	effectSym = ast.PredicateSym{Symbol: "effect", Arity: 2}
	givesSym  = ast.PredicateSym{Symbol: "gives", Arity: 3}
	gotSym    = ast.PredicateSym{Symbol: "got", Arity: 3}
	tellsName = "tells"
)

// maxRounds bounds the evaluate/perform loop so a program that keeps asking
// for new effects cannot run forever.
const maxRounds = 100

// An effect takes the fields a program gives it and returns field/value pairs.
type effectFunc func(dir string, in map[string][]ast.Constant) ([]result, error)

type result struct {
	field string
	value ast.Constant
}

var effects = map[string]effectFunc{
	"list_a_folder": listAFolder,
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

	var lines []string
	for _, pred := range store.ListPredicates() {
		if pred.Symbol != tellsName {
			continue
		}
		for _, args := range facts(store, pred) {
			parts := make([]string, len(args))
			for i, a := range args {
				parts[i] = show(a)
			}
			lines = append(lines, strings.Join(parts, "\t"))
		}
	}
	sort.Strings(lines)
	for _, l := range lines {
		fmt.Println(l)
	}
	return nil
}

// checkHow makes the program's facts about how it is run hold, or says why not.
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

// perform runs the one effect a doing names, with the fields it gives.
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

// listAFolder gives one "file" per entry of the folder that is not itself a
// folder. The folder is read relative to the program's own directory, and
// each path is the folder joined with the entry's name.
func listAFolder(dir string, in map[string][]ast.Constant) ([]result, error) {
	folders := in["folder"]
	if len(folders) != 1 {
		return nil, fmt.Errorf("list_a_folder needs exactly one \"folder\", got %d", len(folders))
	}
	folder, err := folders[0].StringValue()
	if err != nil {
		return nil, fmt.Errorf("list_a_folder: folder must be a string: %w", err)
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
				continue // dangling link
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

// facts returns the arguments of every fact of pred in the store.
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

// str is the text of a string or name constant, or its Mangle form otherwise.
func str(c ast.Constant) string {
	if s, err := c.StringValue(); err == nil {
		return s
	}
	return c.Symbol
}

// show prints a told value: strings as their text, anything else as Mangle.
func show(c ast.Constant) string {
	if c.Type == ast.StringType {
		return c.Symbol
	}
	return c.String()
}
