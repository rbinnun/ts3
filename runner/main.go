package main

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	turnLimit = 1000
	worldName = "world.mg"
)

var realEffects = map[string]func(given map[string]string) ([]string, error){
	"read_the_programs": readThePrograms,
}

type Run struct {
	Turns  [][]string
	Ended  []string
	Failed []string
}

func evaluate(program string) ([]ast.Atom, error) {
	unit, problem := parse.Unit(strings.NewReader(program))
	if problem != nil {
		return nil, problem
	}
	analysed, problem := analysis.AnalyzeOneUnit(unit, nil)
	if problem != nil {
		return nil, problem
	}
	store := factstore.NewSimpleInMemoryStore()
	if problem := engine.EvalProgram(analysed, store, engine.WithCreatedFactLimit(1000000)); problem != nil {
		return nil, problem
	}
	facts := []ast.Atom{}
	problem = factstore.GetAllFacts(store, func(atom ast.Atom) error {
		facts = append(facts, atom)
		return nil
	})
	sort.Slice(facts, func(first, second int) bool { return facts[first].String() < facts[second].String() })
	return facts, problem
}

func named(facts []ast.Atom, name string) []string {
	found := []string{}
	for _, item := range facts {
		if item.Predicate.Symbol == name {
			found = append(found, item.String())
		}
	}
	return found
}

func text(term ast.BaseTerm) string {
	if constant, isConstant := term.(ast.Constant); isConstant {
		if value, problem := constant.StringValue(); problem == nil {
			return value
		}
	}
	return term.String()
}

func describe(source string) ([]string, error) {
	unit, problem := parse.Unit(strings.NewReader(source))
	if problem != nil {
		return nil, problem
	}
	atoms := []ast.Atom{}
	for _, declared := range unit.Decls {
		if declared.DeclaredAtom.Predicate.Symbol != "Package" {
			atoms = append(atoms, declared.DeclaredAtom)
		}
	}
	for _, clause := range unit.Clauses {
		atoms = append(atoms, clause.Head)
		for _, premise := range clause.Premises {
			switch typed := premise.(type) {
			case ast.Atom:
				atoms = append(atoms, typed)
			case ast.NegAtom:
				atoms = append(atoms, typed.Atom)
			}
		}
	}
	facts := []string{}
	for _, atom := range atoms {
		name := atom.Predicate.Symbol
		if strings.HasPrefix(name, ":") {
			continue
		}
		facts = append(facts, fmt.Sprintf("place_count(%q, %d).", name, len(atom.Args)))
		if len(atom.Args) != 3 {
			continue
		}
		if middle, isVariable := atom.Args[1].(ast.Variable); isVariable {
			facts = append(facts, fmt.Sprintf("middle_name(%q, %q).", name, middle.Symbol))
		}
	}
	return facts, nil
}

func readThePrograms(given map[string]string) ([]string, error) {
	root, facts := given["folder"], []string{}
	problem := filepath.WalkDir(root, func(path string, entry fs.DirEntry, problem error) error {
		if problem != nil {
			return problem
		}
		if entry.IsDir() && path != root && strings.HasPrefix(entry.Name(), ".") {
			return filepath.SkipDir
		}
		if entry.IsDir() || !strings.HasSuffix(path, ".mg") {
			return nil
		}
		content, problem := os.ReadFile(path)
		if problem != nil {
			return problem
		}
		described, problem := describe(string(content))
		if problem != nil {
			return fmt.Errorf("%s: %w", path, problem)
		}
		facts = append(facts, described...)
		return nil
	})
	return facts, problem
}

func runMachine(rules, machine, world string) (Run, error) {
	state, ran := world, Run{}
	for turn := 0; turn < turnLimit; turn++ {
		facts, problem := evaluate(rules + "\n" + machine + "\n" + state)
		if problem != nil {
			return ran, fmt.Errorf("turn %d: %w", turn, problem)
		}
		wanting := []ast.Atom{}
		for _, item := range facts {
			if item.Predicate.Symbol == "wants" {
				wanting = append(wanting, item)
			}
		}
		switch {
		case len(wanting) == 0:
			ran.Ended = append(named(facts, "file"), named(facts, "tells")...)
			ran.Failed = named(facts, "fails")
			return ran, nil
		case len(wanting) > 1:
			return ran, fmt.Errorf("turn %d: the machine wants %d things at once: %s", turn, len(wanting),
				strings.Join(named(facts, "wants"), " "))
		}
		doing, effect := wanting[0].Args[0], text(wanting[0].Args[1])
		lines, given := []string{wanting[0].String()}, map[string]string{}
		for _, item := range facts {
			if item.Predicate.Symbol == "gives" && item.Args[0].Equals(doing) {
				lines, given[text(item.Args[1])] = append(lines, item.String()), text(item.Args[2])
			}
		}
		ran.Turns = append(ran.Turns, lines)
		next := []string{}
		for _, item := range facts {
			if rest, found := strings.CutPrefix(item.String(), "next_"); found {
				next = append(next, rest+".")
			}
		}
		if real, found := realEffects[effect]; found {
			made, problem := real(given)
			if problem != nil {
				return ran, fmt.Errorf("turn %d: %s: %w", turn, effect, problem)
			}
			next = append(next, made...)
		}
		state = strings.Join(next, "\n") + "\n"
	}
	return ran, fmt.Errorf("the machine still wants something after %d turns", turnLimit)
}

func programIn(folder, leftOut string) (string, error) {
	paths, problem := filepath.Glob(filepath.Join(folder, "*.mg"))
	if problem != nil {
		return "", problem
	}
	sort.Strings(paths)
	program := []string{}
	for _, path := range paths {
		if filepath.Base(path) == leftOut {
			continue
		}
		content, problem := os.ReadFile(path)
		if problem != nil {
			return "", problem
		}
		program = append(program, string(content))
	}
	return strings.Join(program, "\n"), nil
}

func runFolders(runnerFolder, machineFolder string) (Run, error) {
	rules, problem := programIn(runnerFolder, "")
	if problem != nil {
		return Run{}, problem
	}
	machine, problem := programIn(machineFolder, worldName)
	if problem != nil {
		return Run{}, problem
	}
	world, problem := os.ReadFile(filepath.Join(machineFolder, worldName))
	if problem != nil && !errors.Is(problem, fs.ErrNotExist) {
		return Run{}, problem
	}
	return runMachine(rules, machine, string(world))
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: ./run machine_folder")
		os.Exit(64)
	}
	ran, problem := runFolders(os.Args[1], os.Args[2])
	for turn, lines := range ran.Turns {
		fmt.Printf("turn %d: %s\n", turn, strings.Join(lines, "\n        "))
	}
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(70)
	}
	fmt.Printf("after %d turns:\n", len(ran.Turns))
	for _, item := range append(ran.Ended, ran.Failed...) {
		fmt.Println(item)
	}
	if len(ran.Failed) > 0 {
		os.Exit(1)
	}
}
