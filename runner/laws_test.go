package main

import (
	"io/fs"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func programsIn(test *testing.T, root string) map[string]string {
	found := map[string]string{}
	problem := filepath.WalkDir(root, func(path string, entry fs.DirEntry, problem error) error {
		if problem != nil {
			return problem
		}
		if entry.IsDir() && path != root && strings.HasPrefix(entry.Name(), ".") {
			return filepath.SkipDir
		}
		if !entry.IsDir() && strings.HasSuffix(path, ".mg") {
			found[path] = readFor(test, path)
		}
		return nil
	})
	if problem != nil {
		test.Fatal(problem)
	}
	return found
}

func brokenFor(test *testing.T, programs map[string]string) []string {
	broken, problem := brokenLaws(readFor(test, "../laws.mg"), programs)
	if problem != nil {
		test.Fatal(problem)
	}
	return broken
}

func TestEveryProgramKeepsTheLaws(test *testing.T) {
	programs := programsIn(test, "..")
	if len(programs) < 4 {
		test.Fatalf("found only %d programs", len(programs))
	}
	if broken := brokenFor(test, programs); len(broken) > 0 {
		test.Errorf("broken: %v", broken)
	}
}

func TestAFactWithFourPlacesIsNotSmall(test *testing.T) {
	broken := brokenFor(test, map[string]string{"wide.mg": `wants(Doing, Effect, Path, Content) :- asked(Doing, Effect, Path, Content).`})
	expected := []string{`violation("every_fact_is_small","asked")`, `violation("every_fact_is_small","wants")`}
	if !reflect.DeepEqual(broken, expected) {
		test.Errorf("broken: %v, want %v", broken, expected)
	}
}

func TestAThreePlaceFactWithoutALabelInTheMiddleIsNotSmall(test *testing.T) {
	broken := brokenFor(test, map[string]string{"owned.mg": `file(Path, Content, Owner) :- stored(Path, Content, Owner).`})
	expected := []string{`violation("every_fact_is_small","file")`, `violation("every_fact_is_small","stored")`}
	if !reflect.DeepEqual(broken, expected) {
		test.Errorf("broken: %v, want %v", broken, expected)
	}
}

func TestAThreePlaceFactWithALabelInTheMiddleIsSmall(test *testing.T) {
	if broken := brokenFor(test, map[string]string{"labelled.mg": `got(Doing, Field, Value) :- gives(Doing, Field, Value).`}); len(broken) > 0 {
		test.Errorf("broken: %v", broken)
	}
}
