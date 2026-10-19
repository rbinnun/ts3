package main

import (
	"bufio"
	"bytes"
	"errors"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"sync"
)

type result struct {
	field string
	value Value
}

type toolbox struct {
	m       *Machine
	adds    map[Value][][2]string
	catalog map[string]bool
}

func (m *Machine) toolbox(db *DB) *toolbox {
	box := &toolbox{m: m, adds: map[Value][][2]string{}, catalog: map[string]bool{}}
	for _, b := range db.ask(qAddsLine) {
		box.adds[b["change"]] = append(box.adds[b["change"]], [2]string{b.text("file"), b.text("line")})
	}
	for _, b := range db.ask(qCatalog) {
		box.catalog[b.text("tool")] = true
	}
	return box
}

func (m *Machine) runCalls(db *DB, todo []call) []entry {
	box := m.toolbox(db)
	results := make([][]entry, len(todo))
	var wg sync.WaitGroup
	sem := make(chan struct{}, 4)
	for i, c := range todo {
		wg.Add(1)
		go func(i int, c call) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()
			for _, r := range box.run(c.tool.Text(), c.input) {
				results[i] = append(results[i], entry{fact("returned", c.command, Str(r.field), r.value), m.toolsName})
			}
		}(i, c)
	}
	wg.Wait()
	var out []entry
	for _, r := range results {
		out = append(out, r...)
	}
	return out
}

func (box *toolbox) run(tool string, input Value) []result {
	if !box.catalog[tool] {
		return nil
	}
	switch tool {
	case "list":
		return box.list(input)
	case "find go comments":
		return box.comments(input)
	case "find go functions":
		return box.functions(input)
	case "try":
		return box.try(input)
	}
	box.m.problem("tools.go has no tool named " + tool)
	return nil
}

func (box *toolbox) list(input Value) []result {
	if input.Text() != "the folder" {
		box.m.problem("list lists the folder, not " + input.Text())
		return nil
	}
	var out []result
	filepath.WalkDir(box.m.levelDir, func(p string, d fs.DirEntry, err error) error {
		if err != nil || !d.Type().IsRegular() {
			return nil
		}
		if rel, err := filepath.Rel(box.m.root, p); err == nil {
			out = append(out, result{"file", Str(filepath.ToSlash(rel))})
		}
		return nil
	})
	return out
}

func (box *toolbox) comments(input Value) []result {
	path, ok := within(box.m.root, input.Text())
	if !ok {
		box.m.problem(input.Text() + " is not in the folder that holds the level folders")
		return nil
	}
	src, err := os.ReadFile(path)
	if err != nil {
		box.m.problem(input.Text() + " cannot be read")
		return nil
	}
	fset := token.NewFileSet()
	file := fset.AddFile(path, -1, len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			break
		}
		if tok == token.COMMENT {
			out = append(out, result{"comment", Str(lit)})
		}
	}
	return out
}

func (box *toolbox) functions(input Value) []result {
	path, ok := within(box.m.root, input.Text())
	if !ok {
		box.m.problem(input.Text() + " is not in the folder that holds the level folders")
		return nil
	}
	src, err := os.ReadFile(path)
	if err != nil {
		box.m.problem(input.Text() + " cannot be read")
		return nil
	}
	file, err := parser.ParseFile(token.NewFileSet(), path, src, parser.SkipObjectResolution)
	if err != nil {
		box.m.problem(input.Text() + " cannot be read as go")
		return nil
	}
	var out []result
	for _, d := range file.Decls {
		f, ok := d.(*ast.FuncDecl)
		if !ok {
			continue
		}
		name := f.Name.Name
		if f.Recv != nil && len(f.Recv.List) > 0 {
			name = receiverName(f.Recv.List[0].Type) + "." + name
		}
		out = append(out, result{"function", Str(name)})
	}
	return out
}

func receiverName(t ast.Expr) string {
	switch x := t.(type) {
	case *ast.StarExpr:
		return receiverName(x.X)
	case *ast.ParenExpr:
		return receiverName(x.X)
	case *ast.IndexExpr:
		return receiverName(x.X)
	case *ast.IndexListExpr:
		return receiverName(x.X)
	case *ast.Ident:
		return x.Name
	}
	return ""
}

func copyTree(from, to string) error {
	return filepath.WalkDir(from, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(from, p)
		if err != nil {
			return err
		}
		if rel != "." && filepath.Dir(rel) == "." && strings.HasPrefix(d.Name(), ".") {
			if d.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		target := filepath.Join(to, rel)
		if d.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		if !d.Type().IsRegular() {
			return nil
		}
		data, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		return os.WriteFile(target, data, 0o644)
	})
}

func appendLine(path, line string) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	old, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	return os.WriteFile(path, append(old, []byte(line+"\n")...), 0o644)
}

func (box *toolbox) try(input Value) []result {
	m := box.m
	change := input.Text()
	if m.change {
		m.problem("a change does not try the change " + change)
		return nil
	}
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		m.problem("tools.go cannot make a folder to try " + change)
		return nil
	}
	defer os.RemoveAll(dir)
	if err := copyTree(m.root, dir); err != nil {
		m.problem("tools.go cannot copy the levels to try " + change + ": " + err.Error())
		return nil
	}
	for _, l := range box.adds[input] {
		p, ok := within(dir, l[0])
		if !ok {
			m.problem(change + " adds a line to " + l[0] + ", which is not in the folder that holds the level folders")
			return nil
		}
		if err := appendLine(p, l[1]); err != nil {
			m.problem(change + " cannot add a line to " + l[0])
			return nil
		}
	}
	cmd := exec.Command(m.exe, "-change", filepath.Join(dir, filepath.Base(m.machineDir)))
	cmd.Dir = filepath.Join(dir, m.level)
	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			m.problem("tools.go cannot run engine.go to try " + change)
			return nil
		}
		code = exit.ExitCode()
	}
	laws := map[string]bool{}
	explained := map[string]bool{}
	lines := bufio.NewScanner(&stdout)
	lines.Buffer(make([]byte, 1<<20), 1<<26)
	for lines.Scan() {
		a, err := parseAtom(lines.Text())
		if err != nil || len(a.Args) != 2 {
			continue
		}
		switch a.Pred {
		case "breaks":
			if !a.Args[1].IsBlank() {
				laws[a.Args[1].Val.Text()] = true
			}
		case "holds because":
			explained[renderAtom(a, false)] = true
		}
	}
	var out []result
	for _, law := range sortedKeys(laws) {
		out = append(out, result{"broke", Str(law)})
	}
	out = append(out, result{"exit code", Int(int64(code))})
	for _, e := range sortedKeys(explained) {
		out = append(out, result{"explanation", Str(e)})
	}
	return out
}

func sortedKeys(set map[string]bool) []string {
	out := make([]string, 0, len(set))
	for k := range set {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}
