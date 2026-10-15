package main

import (
	"fmt"
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

const turnLimit = 1000

type Run struct {
	Turns [][]string
	Ended []string
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

func givenFor(facts []ast.Atom, doing ast.BaseTerm) []string {
	found := []string{}
	for _, item := range facts {
		if item.Predicate.Symbol == "gives" && item.Args[0].Equals(doing) {
			found = append(found, item.String())
		}
	}
	return found
}

func runMachine(step, machine, world string) (Run, error) {
	state, ran := world, Run{}
	for turn := 0; turn < turnLimit; turn++ {
		facts, problem := evaluate(machine + "\n" + step + "\n" + state)
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
			return ran, nil
		case len(wanting) > 1:
			return ran, fmt.Errorf("turn %d: the machine wants %d things at once: %s", turn, len(wanting),
				strings.Join(named(facts, "wants"), " "))
		}
		ran.Turns = append(ran.Turns, append([]string{wanting[0].String()}, givenFor(facts, wanting[0].Args[0])...))
		next := []string{}
		for _, item := range facts {
			if rest, found := strings.CutPrefix(item.String(), "next_"); found {
				next = append(next, rest+".")
			}
		}
		state = strings.Join(next, "\n") + "\n"
	}
	return ran, fmt.Errorf("the machine still wants something after %d turns", turnLimit)
}

func readEach(paths ...string) ([]string, error) {
	contents := []string{}
	for _, path := range paths {
		content, problem := os.ReadFile(path)
		if problem != nil {
			return nil, problem
		}
		contents = append(contents, string(content))
	}
	return contents, nil
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: ./run machine_folder")
		os.Exit(64)
	}
	read, problem := readEach(os.Args[1], filepath.Join(os.Args[2], "machine.mg"), filepath.Join(os.Args[2], "world.mg"))
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(70)
	}
	ran, problem := runMachine(read[0], read[1], read[2])
	for turn, lines := range ran.Turns {
		fmt.Printf("turn %d: %s\n", turn, strings.Join(lines, "\n        "))
	}
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(1)
	}
	fmt.Printf("after %d turns:\n", len(ran.Turns))
	for _, item := range ran.Ended {
		fmt.Println(item)
	}
}
