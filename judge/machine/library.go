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

var library = map[string]func(root, doing, target string) ([]string, error){
	"list_a_folder":      listAFolder,
	"break_up_a_program": breakUpAProgram,
	"find_comments":      findComments,
}

var mangleComment = regexp.MustCompile("\"(?:\\\\.|[^\"\\\\])*\"|'(?:\\\\.|[^'\\\\])*'|`(?:\\\\.|[^`\\\\])*`|(#[^\\n]*)")

func listAFolder(root, doing, folder string) ([]string, error) {
	start, facts := filepath.Join(root, folder), []string{}
	problem := filepath.WalkDir(start, func(path string, entry fs.DirEntry, problem error) error {
		if problem != nil {
			return problem
		}
		if path != start && strings.HasPrefix(entry.Name(), ".") {
			if entry.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		if entry.IsDir() {
			return nil
		}
		relative, problem := filepath.Rel(root, path)
		if problem != nil {
			return problem
		}
		facts = append(facts, fmt.Sprintf("got(%q, %q, %q).", doing, "file", filepath.ToSlash(relative)))
		return nil
	})
	return facts, problem
}

func breakUpAProgram(root, doing, path string) ([]string, error) {
	content, problem := os.ReadFile(filepath.Join(root, path))
	if problem != nil {
		return nil, problem
	}
	return describe(path, string(content))
}

func findComments(root, doing, path string) ([]string, error) {
	content, problem := os.ReadFile(filepath.Join(root, path))
	if problem != nil {
		return nil, problem
	}
	facts := []string{}
	for _, line := range commentLines(path, string(content)) {
		facts = append(facts, fmt.Sprintf("comment_line(%q, %d).", path, line))
	}
	return facts, nil
}

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
