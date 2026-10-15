package main

import (
	"os"
	"reflect"
	"slices"
	"strings"
	"testing"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

func brokenLaws(test *testing.T, program string) []string {
	laws, problem := os.ReadFile("../world_laws.mg")
	if problem != nil {
		test.Fatal(problem)
	}
	facts, problem := describe(program)
	if problem != nil {
		test.Fatal(problem)
	}
	unit, problem := parse.Unit(strings.NewReader(string(laws) + "\n" + strings.Join(facts, "\n") + "\n"))
	if problem != nil {
		test.Fatal(problem)
	}
	analysed, problem := analysis.AnalyzeOneUnit(unit, nil)
	if problem != nil {
		test.Fatal(problem)
	}
	store := factstore.NewSimpleInMemoryStore()
	if problem := engine.EvalProgram(analysed, store); problem != nil {
		test.Fatal(problem)
	}
	broken := []string{}
	store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "violation", Arity: 2}), func(atom ast.Atom) error {
		broken = append(broken, atom.String())
		return nil
	})
	slices.Sort(broken)
	return broken
}

func TestTheProgramsOfTheRepositoryAreRead(test *testing.T) {
	facts, problem := readThePrograms("../../..")
	if problem != nil {
		test.Fatal(problem)
	}
	for _, fact := range []string{`place_count("version", 3).`, `middle_name("version", "Path").`, `place_count("proven", 0).`} {
		if !slices.Contains(facts, fact) {
			test.Errorf("missing %s", fact)
		}
	}
}

func TestAFactWithFourPlacesIsNotSmall(test *testing.T) {
	broken := brokenLaws(test, `wants(Doing, Effect, Path, Content) :- asked(Doing, Effect, Path, Content).`)
	expected := []string{`violation("every_fact_is_small","asked")`, `violation("every_fact_is_small","wants")`}
	if !reflect.DeepEqual(broken, expected) {
		test.Errorf("broken: %v, want %v", broken, expected)
	}
}

func TestAThreePlaceFactWithoutALabelInTheMiddleIsNotSmall(test *testing.T) {
	broken := brokenLaws(test, `file(Path, Content, Owner) :- stored(Path, Content, Owner).`)
	expected := []string{`violation("every_fact_is_small","file")`, `violation("every_fact_is_small","stored")`}
	if !reflect.DeepEqual(broken, expected) {
		test.Errorf("broken: %v, want %v", broken, expected)
	}
}

func TestAThreePlaceFactWithALabelInTheMiddleIsSmall(test *testing.T) {
	program := `got(Doing, Field, Value) :- gives(Doing, Field, Value).` + "\n" + `version(Doing, Path, Content) :- kept(Doing, Path, Content).`
	if broken := brokenLaws(test, program); len(broken) > 0 {
		test.Errorf("broken: %v", broken)
	}
}
