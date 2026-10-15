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
	machine := `wants("one", "read_a_file") :- !done("one").` + "\n" + `wants("two", "read_a_file") :- !done("two").`
	_, problem := runMachine(readFor(test, "step.mg"), machine, "")
	if problem == nil || !strings.Contains(problem.Error(), "wants 2 things at once") {
		test.Errorf("expected the run to stop on two wants at once, got %v", problem)
	}
}
