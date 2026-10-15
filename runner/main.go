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
	Wanted []string
	Ended  []string
}

func evaluate(program string) ([]string, error) {
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
	facts := []string{}
	problem = factstore.GetAllFacts(store, func(atom ast.Atom) error {
		facts = append(facts, atom.String())
		return nil
	})
	sort.Strings(facts)
	return facts, problem
}

func named(facts []string, name string) []string {
	found := []string{}
	for _, item := range facts {
		if strings.HasPrefix(item, name+"(") {
			found = append(found, item)
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
		wants := named(facts, "wants")
		switch {
		case len(wants) == 0:
			ran.Ended = append(named(facts, "file"), named(facts, "tells")...)
			return ran, nil
		case len(wants) > 1:
			return ran, fmt.Errorf("turn %d: the machine wants %d things at once: %s", turn, len(wants), strings.Join(wants, " "))
		}
		ran.Wanted = append(ran.Wanted, wants[0])
		next := []string{}
		for _, item := range facts {
			if rest, found := strings.CutPrefix(item, "next_"); found {
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
	for turn, wanted := range ran.Wanted {
		fmt.Printf("turn %d: %s\n", turn, wanted)
	}
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(1)
	}
	fmt.Printf("after %d turns:\n", len(ran.Wanted))
	for _, item := range ran.Ended {
		fmt.Println(item)
	}
}
