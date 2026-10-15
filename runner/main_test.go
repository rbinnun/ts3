package main

import (
	"os"
	"reflect"
	"strings"
	"testing"
)

func readFor(test *testing.T, path string) string {
	content, problem := os.ReadFile(path)
	if problem != nil {
		test.Fatal(problem)
	}
	return string(content)
}

func TestCopyNotesReadsThenCopiesThenTells(test *testing.T) {
	ran, problem := runMachine(readFor(test, "step.mg"), readFor(test, "../machines/copy_notes/machine.mg"),
		readFor(test, "../machines/copy_notes/world.mg"))
	if problem != nil {
		test.Fatal(problem)
	}
	wanted := []string{`wants("read notes","read_a_file","notes.txt","")`, `wants("copy notes","write_a_file","copy.txt","hello")`}
	if !reflect.DeepEqual(ran.Wanted, wanted) {
		test.Errorf("wanted %v, got %v", wanted, ran.Wanted)
	}
	ended := []string{`file("copy.txt","hello")`, `file("notes.txt","hello")`, `tells("notes say: hello")`}
	if !reflect.DeepEqual(ran.Ended, ended) {
		test.Errorf("ended with %v, want %v", ran.Ended, ended)
	}
}

func TestAMachineThatWantsTwoThingsAtOnceIsStopped(test *testing.T) {
	machine := `wants("one", "read_a_file", "a.txt", "") :- !done("one").` + "\n" + `wants("two", "read_a_file", "b.txt", "") :- !done("two").`
	_, problem := runMachine(readFor(test, "step.mg"), machine, "")
	if problem == nil || !strings.Contains(problem.Error(), "wants 2 things at once") {
		test.Errorf("expected the run to stop on two wants at once, got %v", problem)
	}
}
