package main

import (
	"bytes"
	"errors"
	"fmt"
	"go/scanner"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"

	"github.com/google/mangle/ast"
	"github.com/google/mangle/factstore"
)

type result struct {
	returned []ast.Atom
	problems []string
}

type workshop struct {
	store  factstore.ReadOnlyFactStore
	change bool
	order  map[string]int
}

var commentFinders = map[string]func([]byte) []string{
	"go": goComments,
	"sh": shComments,
}

func (w workshop) use(c call) result {
	switch c.tool {
	case "list":
		return w.list(c)
	case "try":
		return w.try(c)
	}
	languages := textsOf(w.store, "finds comments in", c.tool)
	if len(languages) == 1 {
		if find, ok := commentFinders[languages[0]]; ok {
			return w.findComments(c, find)
		}
	}
	return failure(fmt.Sprintf("%s calls %s, which tools.go does not have", showCommand(c), c.tool))
}

func showCommand(c call) string {
	if s, ok := textOf(c.command); ok {
		return s
	}
	return c.command.String()
}

func failure(text string) result {
	return result{problems: []string{text}}
}

func returnedFact(c call, field string, value ast.Constant) ast.Atom {
	return fact("returned", c.command, ast.String(field), value)
}

func (w workshop) list(c call) result {
	if c.input != "the folder" {
		return failure(fmt.Sprintf("%s asks list for %s, but list only lists the folder", showCommand(c), c.input))
	}
	entries, err := os.ReadDir(".")
	if err != nil {
		return failure(fmt.Sprintf("list cannot read the folder: %v", err))
	}
	var r result
	for _, e := range entries {
		if e.Type().IsRegular() {
			r.returned = append(r.returned, returnedFact(c, "file", ast.String(e.Name())))
		}
	}
	return r
}

func insideFolder(name string) bool {
	return name != "" && name != "." && name != ".." && filepath.Base(name) == name
}

func (w workshop) findComments(c call, find func([]byte) []string) result {
	if !insideFolder(c.input) {
		return failure(fmt.Sprintf("%s asks %s about %s, which is not a file in the folder", showCommand(c), c.tool, c.input))
	}
	src, err := os.ReadFile(c.input)
	if err != nil {
		return failure(fmt.Sprintf("%s cannot read %s: %v", c.tool, c.input, err))
	}
	var r result
	for _, text := range find(src) {
		r.returned = append(r.returned, returnedFact(c, "comment", ast.String(text)))
	}
	return r
}

func goComments(src []byte) []string {
	fset := token.NewFileSet()
	file := fset.AddFile("", fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, scanner.ScanComments)
	var out []string
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, lit)
		}
	}
}

func shComments(src []byte) []string {
	s := string(src)
	var out []string
	var quote byte
	for i := 0; i < len(s); i++ {
		ch := s[i]
		switch {
		case quote == '\'':
			if ch == '\'' {
				quote = 0
			}
		case quote == '"':
			if ch == '\\' {
				i++
			} else if ch == '"' {
				quote = 0
			}
		case ch == '\\':
			i++
		case ch == '\'' || ch == '"':
			quote = ch
		case ch == '#' && (i == 0 || strings.IndexByte(" \t\n;&|()<>", s[i-1]) >= 0):
			end := strings.IndexByte(s[i:], '\n')
			if end < 0 {
				end = len(s) - i
			}
			out = append(out, strings.TrimRight(s[i:i+end], "\r"))
			i += end - 1
		}
	}
	return out
}

func (w workshop) try(c call) result {
	if w.change {
		return failure(fmt.Sprintf("%s calls try in a run that is itself a change, and a change does not try changes", showCommand(c)))
	}
	scripts := textsOf(w.store, "runs", c.tool)
	if len(scripts) != 1 {
		return failure(fmt.Sprintf("%s runs %d files, not one", c.tool, len(scripts)))
	}
	places := textsOf(w.store, "reads", c.tool)
	if len(places) == 0 {
		return failure(fmt.Sprintf("%s is not told what to read", c.tool))
	}
	var lines []ast.Atom
	for _, f := range factsOf(w.store, "adds line", 3) {
		if change, ok := textOf(f.Args[0]); ok && change == c.input {
			lines = append(lines, f)
		}
	}
	sort.SliceStable(lines, func(i, j int) bool {
		return w.rank(lines[i]) < w.rank(lines[j])
	})
	dir, err := os.MkdirTemp("", "change-")
	if err != nil {
		return failure(fmt.Sprintf("try cannot make a copy of the folder: %v", err))
	}
	defer os.RemoveAll(dir)
	if err := copyFolder(dir); err != nil {
		return failure(fmt.Sprintf("try cannot copy the folder: %v", err))
	}
	for _, f := range lines {
		file, ok1 := textOf(f.Args[1])
		line, ok2 := textOf(f.Args[2])
		if !ok1 || !ok2 || !insideFolder(file) {
			return failure(fmt.Sprintf("%s adds a line to %s, which is not a file in the folder", c.input, f.Args[1].String()))
		}
		if err := appendLine(filepath.Join(dir, file), line); err != nil {
			return failure(fmt.Sprintf("try cannot add a line to %s: %v", file, err))
		}
	}
	cmd := exec.Command("sh", scripts[0], "change")
	cmd.Dir = dir
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return failure(fmt.Sprintf("try cannot run %s: %v", scripts[0], err))
		}
		code = exit.ExitCode()
	}
	var text strings.Builder
	var r result
	for _, place := range places {
		switch place {
		case "standard output":
			text.WriteString(stdout.String() + "\n")
		case "standard error":
			text.WriteString(stderr.String() + "\n")
		default:
			r.problems = append(r.problems, fmt.Sprintf("%s cannot read %s", c.tool, place))
		}
	}
	r.returned = append(r.returned, returnedFact(c, "exit code", ast.Number(int64(code))))
	explanations, laws := readExplanations(text.String())
	for _, law := range laws {
		r.returned = append(r.returned, returnedFact(c, "broke", ast.String(law)))
	}
	for _, e := range explanations {
		r.returned = append(r.returned, returnedFact(c, "explanation", ast.String(e)))
	}
	return r
}

func (w workshop) rank(f ast.Atom) int {
	if i, ok := w.order[f.String()]; ok {
		return i
	}
	return unstated
}

func copyFolder(dir string) error {
	entries, err := os.ReadDir(".")
	if err != nil {
		return err
	}
	for _, e := range entries {
		if !e.Type().IsRegular() {
			continue
		}
		info, err := e.Info()
		if err != nil {
			return err
		}
		data, err := os.ReadFile(e.Name())
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(dir, e.Name()), data, info.Mode().Perm()); err != nil {
			return err
		}
	}
	return nil
}

func appendLine(path, line string) error {
	perm := os.FileMode(0o644)
	if info, err := os.Stat(path); err == nil {
		perm = info.Mode().Perm()
	}
	data, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line...)
	data = append(data, '\n')
	return os.WriteFile(path, data, perm)
}

func readExplanations(text string) ([]string, []string) {
	rules, _ := readPlain("output", text)
	explanations := map[string]bool{}
	laws := map[string]bool{}
	for _, r := range rules {
		if r.broken || len(r.body) > 0 || r.head.Predicate != symbolOf("holds because", 2) {
			continue
		}
		explanations[r.text[0]] = true
		stated, ok := stringOf(r.head.Args[0])
		if !ok {
			continue
		}
		t, err := parseLine(stated)
		if err != nil {
			continue
		}
		if a, ok := t.(ast.Atom); ok && a.Predicate == symbolOf("breaks", 2) {
			if law, ok := textOf(a.Args[1]); ok {
				laws[law] = true
			}
		}
	}
	return sortedKeys(explanations), sortedKeys(laws)
}

func sortedKeys(m map[string]bool) []string {
	var out []string
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}
