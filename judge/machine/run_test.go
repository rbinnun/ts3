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

var (
	languageLaws = []string{"../universal_laws.mg", "../../worlds/language_contract/world_laws.mg"}
	universeLaws = []string{"../universal_laws.mg", "../../world_laws.mg"}
)

func broken(test *testing.T, law string, lawFiles []string, facts []string) []string {
	programs := []string{}
	for _, path := range lawFiles {
		content, problem := os.ReadFile(path)
		if problem != nil {
			test.Fatal(problem)
		}
		programs = append(programs, string(content))
	}
	unit, problem := parse.Unit(strings.NewReader(strings.Join(append(programs, facts...), "\n") + "\n"))
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
	found := []string{}
	store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "violation", Arity: 2}), func(atom ast.Atom) error {
		if named, isConstant := atom.Args[0].(ast.Constant); isConstant {
			if text, problem := named.StringValue(); problem == nil && text == law {
				found = append(found, atom.String())
			}
		}
		return nil
	})
	slices.Sort(found)
	return found
}

func described(test *testing.T, program string) []string {
	facts, problem := describe("program.mg", program)
	if problem != nil {
		test.Fatal(problem)
	}
	return facts
}

func expectBroken(test *testing.T, law string, lawFiles []string, facts []string, expected ...string) {
	if got := broken(test, law, lawFiles, facts); !reflect.DeepEqual(got, expected) && (len(got) > 0 || len(expected) > 0) {
		test.Errorf("%s broken at %v, want %v", law, got, expected)
	}
}

func TestTheUniversesMachineLoadsEveryFileAndBreaksUpEveryProgram(test *testing.T) {
	machine, problem := os.ReadFile("../../world_machine.mg")
	if problem != nil {
		test.Fatal(problem)
	}
	facts, problem := runMachine("../..", string(machine))
	if problem != nil {
		test.Fatal(problem)
	}
	for _, fact := range []string{`universe_file("run.me").`, `universe_file("judge/machine/load.mg").`, `universe_file("judge/machine/go.sum").`,
		`place_count("version",3).`, `middle_name("version","Path").`, `declares("world_laws.mg","universe_file").`,
		`defines("judge/universal_laws.mg","proven").`, `mentions("judge/universal_laws.mg","violation").`} {
		if !slices.Contains(facts, fact) {
			test.Errorf("missing %s", fact)
		}
	}
	for _, fact := range facts {
		if strings.HasPrefix(fact, "comment_line(") {
			test.Errorf("the universe has a comment: %s", fact)
		}
	}
}

func TestAMachineWantingWhatTheLibraryLacksIsStopped(test *testing.T) {
	_, problem := runMachine("../..", "Decl got(Doing, Field, Value).\ndoes(\"fly away\").\neffect(\"fly away\", \"fly\").\n")
	if problem == nil || !strings.Contains(problem.Error(), "no effect of the library") {
		test.Errorf("expected the run to stop on an effect the library lacks, got %v", problem)
	}
}

func TestAFactWithFourPlacesIsNotSmall(test *testing.T) {
	expectBroken(test, "every_fact_is_small", languageLaws,
		described(test, `wants(Doing, Effect, Path, Content) :- asked(Doing, Effect, Path, Content).`),
		`violation("every_fact_is_small","asked")`, `violation("every_fact_is_small","wants")`)
}

func TestAThreePlaceFactWithoutALabelInTheMiddleIsNotSmall(test *testing.T) {
	expectBroken(test, "every_fact_is_small", languageLaws, described(test, `file(Path, Content, Owner) :- stored(Path, Content, Owner).`),
		`violation("every_fact_is_small","file")`, `violation("every_fact_is_small","stored")`)
}

func TestAThreePlaceFactWithALabelInTheMiddleIsSmall(test *testing.T) {
	expectBroken(test, "every_fact_is_small", languageLaws,
		described(test, `got(Doing, Field, Value) :- gives(Doing, Field, Value).`+"\n"+`version(Doing, Path, Content) :- kept(Doing, Path, Content).`))
}

func TestAPredicateNothingDefinesIsNotDefined(test *testing.T) {
	expectBroken(test, "every_predicate_is_defined", languageLaws, described(test, `wanted(Thing) :- asked(Thing).`),
		`violation("every_predicate_is_defined","program.mg: asked")`)
}

func TestAPredicateNothingUsesIsNotUsed(test *testing.T) {
	expectBroken(test, "every_predicate_is_used", languageLaws, described(test, `wanted(Thing) :- asked(Thing).`),
		`violation("every_predicate_is_used","program.mg: wanted")`)
}

func TestWhatTheJudgeReadsIsUsed(test *testing.T) {
	facts := described(test, `tells(Line) :- said(Line).`+"\n"+`said("hi").`)
	expectBroken(test, "every_predicate_is_defined", languageLaws, facts)
	expectBroken(test, "every_predicate_is_used", languageLaws, facts)
}

func TestACommentIsFoundInMangleButNotInAString(test *testing.T) {
	if lines := commentLines("a.mg", "a(1). # a note\nb(\"# not a note\").\n"); !reflect.DeepEqual(lines, []int{1}) {
		test.Errorf("comment lines %v, want [1]", lines)
	}
}

func TestACommentIsFoundInGoButNotInAString(test *testing.T) {
	source := "package main\n\n// a note\nvar text = \"// not a note\"\n/* one\ntwo */\n"
	if lines := commentLines("a.go", source); !reflect.DeepEqual(lines, []int{3, 5, 6}) {
		test.Errorf("comment lines %v, want [3 5 6]", lines)
	}
}

func TestACommentBreaksTheUniverse(test *testing.T) {
	expectBroken(test, "every_file_has_no_comments", universeLaws, []string{`comment_line("a.mg", 1).`},
		`violation("every_file_has_no_comments","a.mg")`)
}
