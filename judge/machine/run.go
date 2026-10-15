package main

import (
	"fmt"
	"os"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const turnLimit = 10000

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
	if problem := engine.EvalProgram(analysed, store); problem != nil {
		return nil, problem
	}
	facts := []ast.Atom{}
	problem = factstore.GetAllFacts(store, func(atom ast.Atom) error {
		facts = append(facts, atom)
		return nil
	})
	return facts, problem
}

func text(term ast.BaseTerm) string {
	if constant, isConstant := term.(ast.Constant); isConstant {
		if value, problem := constant.StringValue(); problem == nil {
			return value
		}
	}
	return term.String()
}

func runMachine(root, program string) ([]string, error) {
	state, done := []string{}, map[string]bool{}
	for turn := 0; turn < turnLimit; turn++ {
		facts, problem := evaluate(program + "\n" + strings.Join(state, "\n") + "\n")
		if problem != nil {
			return nil, fmt.Errorf("turn %d: %w", turn, problem)
		}
		pending, effects, targets, kept := []string{}, map[string]string{}, map[string]string{}, map[string]bool{}
		for _, item := range facts {
			switch item.Predicate.Symbol {
			case "does":
				if doing := text(item.Args[0]); !done[doing] {
					pending = append(pending, doing)
				}
			case "effect":
				effects[text(item.Args[0])] = text(item.Args[1])
			case "target":
				targets[text(item.Args[0])] = text(item.Args[1])
			case "keeps":
				kept[text(item.Args[0])] = true
			}
		}
		if len(pending) == 0 {
			found := []string{}
			for _, item := range facts {
				if kept[item.Predicate.Symbol] {
					found = append(found, item.String()+".")
				}
			}
			sort.Strings(found)
			return found, nil
		}
		sort.Strings(pending)
		doing := pending[0]
		effect, known := library[effects[doing]]
		if !known {
			return nil, fmt.Errorf("%s wants %q, which is no effect of the library", doing, effects[doing])
		}
		made, problem := effect(root, doing, targets[doing])
		if problem != nil {
			return nil, fmt.Errorf("%s: %w", doing, problem)
		}
		state, done[doing] = append(state, made...), true
	}
	return nil, fmt.Errorf("the machine still wants something after %d turns", turnLimit)
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: runner universe_folder machine_file")
		os.Exit(64)
	}
	program, problem := os.ReadFile(os.Args[2])
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(70)
	}
	facts, problem := runMachine(os.Args[1], string(program))
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(70)
	}
	for _, fact := range facts {
		fmt.Println(fact)
	}
}
