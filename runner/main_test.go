package main

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func runIn(test *testing.T, machineFolder string) Run {
	ran, problem := runFolders(".", machineFolder)
	if problem != nil {
		test.Fatal(problem)
	}
	return ran
}

func TestCopyNotesReadsThenCopiesThenTells(test *testing.T) {
	ran := runIn(test, "../machines/copy_notes")
	turns := [][]string{
		{`wants("read notes","read_a_file")`, `gives("read notes","path","notes.txt")`},
		{`wants("copy notes","write_a_file")`, `gives("copy notes","content","hello")`, `gives("copy notes","path","copy.txt")`},
	}
	if !reflect.DeepEqual(ran.Turns, turns) {
		test.Errorf("turns were %v, want %v", ran.Turns, turns)
	}
	ended := []string{`file("copy.txt","hello")`, `file("notes.txt","hello")`, `tells("notes say: hello")`}
	if !reflect.DeepEqual(ran.Ended, ended) {
		test.Errorf("ended with %v, want %v", ran.Ended, ended)
	}
}

func TestAMachineThatWantsTwoThingsAtOnceIsStopped(test *testing.T) {
	rules, problem := programIn(".", "")
	if problem != nil {
		test.Fatal(problem)
	}
	machine := `wants("one", "read_a_file") :- !done("one").` + "\n" + `wants("two", "read_a_file") :- !done("two").`
	_, problem = runMachine(rules, machine, "")
	if problem == nil || !strings.Contains(problem.Error(), "wants 2 things at once") {
		test.Errorf("expected the run to stop on two wants at once, got %v", problem)
	}
}

func lawsOver(test *testing.T, folder string) Run {
	runnerFolder, problem := filepath.Abs(".")
	if problem != nil {
		test.Fatal(problem)
	}
	lawsFolder := filepath.Join(filepath.Dir(runnerFolder), "machines", "laws")
	test.Chdir(folder)
	ran, problem := runFolders(runnerFolder, lawsFolder)
	if problem != nil {
		test.Fatal(problem)
	}
	return ran
}

func lawsOverOne(test *testing.T, program string) Run {
	folder := test.TempDir()
	if problem := os.WriteFile(filepath.Join(folder, "program.mg"), []byte(program), 0o644); problem != nil {
		test.Fatal(problem)
	}
	return lawsOver(test, folder)
}

func TestEveryProgramInTheRepositoryKeepsTheLaws(test *testing.T) {
	ran := lawsOver(test, "..")
	if len(ran.Failed) > 0 || !reflect.DeepEqual(ran.Ended, []string{`tells("every program keeps the laws")`}) {
		test.Errorf("failed %v, ended %v", ran.Failed, ran.Ended)
	}
}

func TestAFactWithFourPlacesIsNotSmall(test *testing.T) {
	ran := lawsOverOne(test, `wants(Doing, Effect, Path, Content) :- asked(Doing, Effect, Path, Content).`)
	failed := []string{`fails("every_fact_is_small: asked")`, `fails("every_fact_is_small: wants")`}
	if !reflect.DeepEqual(ran.Failed, failed) {
		test.Errorf("failed %v, want %v", ran.Failed, failed)
	}
}

func TestAThreePlaceFactWithoutALabelInTheMiddleIsNotSmall(test *testing.T) {
	ran := lawsOverOne(test, `file(Path, Content, Owner) :- stored(Path, Content, Owner).`)
	failed := []string{`fails("every_fact_is_small: file")`, `fails("every_fact_is_small: stored")`}
	if !reflect.DeepEqual(ran.Failed, failed) {
		test.Errorf("failed %v, want %v", ran.Failed, failed)
	}
}

func TestAThreePlaceFactWithALabelInTheMiddleIsSmall(test *testing.T) {
	if ran := lawsOverOne(test, `got(Doing, Field, Value) :- gives(Doing, Field, Value).`); len(ran.Failed) > 0 {
		test.Errorf("failed %v", ran.Failed)
	}
}
