package main

import (
	"fmt"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/parse"
)

func atomsOf(unit parse.SourceUnit) []ast.Atom {
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
	return atoms
}

func describe(source string) ([]string, error) {
	unit, problem := parse.Unit(strings.NewReader(source))
	if problem != nil {
		return nil, problem
	}
	facts := []string{}
	for _, atom := range atomsOf(unit) {
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

func brokenLaws(laws string, programs map[string]string) ([]string, error) {
	paths := []string{}
	for path := range programs {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	facts := []string{}
	for _, path := range paths {
		described, problem := describe(programs[path])
		if problem != nil {
			return nil, fmt.Errorf("%s: %w", path, problem)
		}
		facts = append(facts, described...)
	}
	derived, problem := evaluate(laws + "\n" + strings.Join(facts, "\n") + "\n")
	if problem != nil {
		return nil, problem
	}
	return named(derived, "violation"), nil
}
