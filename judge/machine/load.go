package main

import (
	"fmt"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const loadedName = "judge/machine/load.mg"

var mangleComment = regexp.MustCompile("\"(?:\\\\.|[^\"\\\\])*\"|'(?:\\\\.|[^'\\\\])*'|`(?:\\\\.|[^`\\\\])*`|(#[^\\n]*)")

func describe(path, source string) ([]string, error) {
	unit, problem := parse.Unit(strings.NewReader(source))
	if problem != nil {
		return nil, problem
	}
	facts := []string{}
	said := func(relation string, atom ast.Atom) {
		name := atom.Predicate.Symbol
		if strings.HasPrefix(name, ":") {
			return
		}
		facts = append(facts, fmt.Sprintf("%s(%q, %q).", relation, path, name), fmt.Sprintf("place_count(%q, %d).", name, len(atom.Args)))
		if len(atom.Args) != 3 {
			return
		}
		if middle, isVariable := atom.Args[1].(ast.Variable); isVariable {
			facts = append(facts, fmt.Sprintf("middle_name(%q, %q).", name, middle.Symbol))
		}
	}
	for _, declared := range unit.Decls {
		if declared.DeclaredAtom.Predicate.Symbol != "Package" {
			said("declares", declared.DeclaredAtom)
		}
	}
	for _, clause := range unit.Clauses {
		said("defines", clause.Head)
		for _, premise := range clause.Premises {
			switch typed := premise.(type) {
			case ast.Atom:
				said("mentions", typed)
			case ast.NegAtom:
				said("mentions", typed.Atom)
			}
		}
	}
	return facts, nil
}

func commentLines(path, source string) []int {
	lines := map[int]bool{}
	if strings.HasSuffix(path, ".go") {
		files := token.NewFileSet()
		var reading scanner.Scanner
		reading.Init(files.AddFile(path, -1, len(source)), []byte(source), nil, scanner.ScanComments)
		for {
			position, kind, text := reading.Scan()
			if kind == token.EOF {
				break
			}
			if kind == token.COMMENT {
				first := files.Position(position).Line
				for line := first; line <= first+strings.Count(text, "\n"); line++ {
					lines[line] = true
				}
			}
		}
	}
	if strings.HasSuffix(path, ".mg") {
		for _, match := range mangleComment.FindAllStringSubmatchIndex(source, -1) {
			if match[2] >= 0 {
				lines[strings.Count(source[:match[2]], "\n")+1] = true
			}
		}
	}
	found := []int{}
	for line := range lines {
		found = append(found, line)
	}
	sort.Ints(found)
	return found
}

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
		relative = filepath.ToSlash(relative)
		if problem != nil || relative == loadedName {
			return problem
		}
		found[fmt.Sprintf("universe_file(%q).", relative)] = true
		if !strings.HasSuffix(path, ".mg") && !strings.HasSuffix(path, ".go") {
			return nil
		}
		content, problem := os.ReadFile(path)
		if problem != nil {
			return problem
		}
		for _, line := range commentLines(relative, string(content)) {
			found[fmt.Sprintf("comment_line(%q, %d).", relative, line)] = true
		}
		if !strings.HasSuffix(path, ".mg") {
			return nil
		}
		described, problem := describe(relative, string(content))
		if problem != nil {
			return fmt.Errorf("%s: %w", relative, problem)
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
