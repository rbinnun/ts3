package main

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/parse"
)

func describe(source string) ([]string, error) {
	unit, problem := parse.Unit(strings.NewReader(source))
	if problem != nil {
		return nil, problem
	}
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
	facts := []string{}
	for _, atom := range atoms {
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

const loadedName = "judge/machine/load.mg"

func loadTheUniverse(root string) ([]string, error) {
	found := map[string]bool{fmt.Sprintf("universe_file(%q).", loadedName): true}
	problem := filepath.WalkDir(root, func(path string, entry fs.DirEntry, problem error) error {
		if problem != nil {
			return problem
		}
		if path != root && strings.HasPrefix(entry.Name(), ".") {
			if entry.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if entry.IsDir() {
			return nil
		}
		relative, problem := filepath.Rel(root, path)
		if problem != nil || filepath.ToSlash(relative) == loadedName {
			return problem
		}
		found[fmt.Sprintf("universe_file(%q).", filepath.ToSlash(relative))] = true
		if !strings.HasSuffix(path, ".mg") {
			return nil
		}
		content, problem := os.ReadFile(path)
		if problem != nil {
			return problem
		}
		described, problem := describe(string(content))
		if problem != nil {
			return fmt.Errorf("%s: %w", path, problem)
		}
		for _, fact := range described {
			found[fact] = true
		}
		return nil
	})
	facts := []string{}
	for fact := range found {
		facts = append(facts, fact)
	}
	sort.Strings(facts)
	return facts, problem
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: load universe_folder")
		os.Exit(64)
	}
	facts, problem := loadTheUniverse(os.Args[1])
	if problem != nil {
		fmt.Fprintf(os.Stderr, "ERROR  %v\n", problem)
		os.Exit(70)
	}
	for _, fact := range facts {
		fmt.Println(fact)
	}
}
