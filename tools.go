package main

import (
	"bytes"
	"context"
	"go/scanner"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"

	"codeberg.org/TauCeti/mangle-go/ast"
)

type returnedValue struct {
	field string
	value ast.Constant
}

func runCalls(k *kb, m *model, calls []ast.Atom) map[string][]ast.Atom {
	out := map[string][]ast.Atom{}
	var mu sync.Mutex
	var wg sync.WaitGroup
	slots := make(chan struct{}, runtime.NumCPU())
	for _, c := range calls {
		wg.Add(1)
		go func(c ast.Atom) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			var atoms []ast.Atom
			for _, v := range runTool(k, m, c) {
				atoms = append(atoms, ast.NewAtom("returned", c.Args[0], ast.String(v.field), v.value))
			}
			mu.Lock()
			out[c.String()] = atoms
			mu.Unlock()
		}(c)
	}
	wg.Wait()
	return out
}

func runTool(k *kb, m *model, call ast.Atom) []returnedValue {
	tool, ok1 := str(call.Args[1])
	input, ok2 := str(call.Args[2])
	if !ok1 || !ok2 {
		return nil
	}
	switch tool {
	case "list":
		return listTool(input)
	case "find go comments":
		return goComments(input)
	case "find sh comments":
		return shComments(input)
	case "try":
		return tryTool(k, m, tool, input)
	}
	return nil
}

func listTool(input string) []returnedValue {
	if input != "the folder" {
		return nil
	}
	entries, err := os.ReadDir(".")
	if err != nil {
		return nil
	}
	var out []returnedValue
	for _, e := range entries {
		out = append(out, returnedValue{"file", ast.String(e.Name())})
	}
	return out
}

func inFolder(name string) bool {
	return name != "" && name != "." && name != ".." && !strings.ContainsAny(name, `/\`)
}

func goComments(file string) []returnedValue {
	if !inFolder(file) {
		return nil
	}
	data, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	fset := token.NewFileSet()
	f := fset.AddFile(file, -1, len(data))
	var s scanner.Scanner
	s.Init(f, data, nil, scanner.ScanComments)
	var out []returnedValue
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, returnedValue{"comment", ast.String(lit)})
		}
	}
}

func shComments(file string) []returnedValue {
	if !inFolder(file) {
		return nil
	}
	data, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	text := string(data)
	var out []returnedValue
	var quote byte
	wordStart := true
	for i := 0; i < len(text); i++ {
		c := text[i]
		switch {
		case quote == '\'':
			if c == '\'' {
				quote = 0
			}
			wordStart = false
		case quote == '"':
			if c == '\\' {
				i++
			} else if c == '"' {
				quote = 0
			}
			wordStart = false
		case c == '\\':
			i++
			wordStart = false
		case c == '\'' || c == '"':
			quote = c
			wordStart = false
		case c == '#' && wordStart:
			end := strings.IndexByte(text[i:], '\n')
			if end < 0 {
				end = len(text)
			} else {
				end += i
			}
			out = append(out, returnedValue{"comment", ast.String(text[i:end])})
			i = end - 1
			wordStart = false
		default:
			wordStart = strings.IndexByte(" \t\n;&|()<>", c) >= 0
		}
	}
	return out
}

func firstString(m *model, sym, subject string) string {
	var found []string
	for _, a := range m.facts(sym, 2) {
		if s, ok := str(a.Args[0]); ok && s == subject {
			if v, ok := str(a.Args[1]); ok {
				found = append(found, v)
			}
		}
	}
	sort.Strings(found)
	if len(found) == 0 {
		return ""
	}
	return found[0]
}

type addedLine struct {
	file string
	line string
	ord  int
}

func addedLines(k *kb, m *model, change string) []addedLine {
	var out []addedLine
	for _, a := range m.facts("adds_line", 3) {
		if s, ok := str(a.Args[0]); !ok || s != change {
			continue
		}
		file, ok1 := a.Args[1].(ast.Constant)
		line, ok2 := a.Args[2].(ast.Constant)
		if !ok1 || !ok2 {
			continue
		}
		f, okf := asText(file)
		l, okl := asText(line)
		if !okf || !okl {
			continue
		}
		ord, ok := k.order[a.String()]
		if !ok {
			ord = 1 << 30
		}
		out = append(out, addedLine{f, l, ord})
	}
	sort.SliceStable(out, func(i, j int) bool {
		if out[i].ord != out[j].ord {
			return out[i].ord < out[j].ord
		}
		return out[i].file+"\n"+out[i].line < out[j].file+"\n"+out[j].line
	})
	return out
}

func copyFolder(from, to string) error {
	if err := os.MkdirAll(to, 0o755); err != nil {
		return err
	}
	entries, err := os.ReadDir(from)
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
		data, err := os.ReadFile(filepath.Join(from, e.Name()))
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(to, e.Name()), data, info.Mode().Perm()); err != nil {
			return err
		}
	}
	return nil
}

func appendLine(folder, file, line string) error {
	path := filepath.Join(folder, file)
	data, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line...)
	data = append(data, '\n')
	return os.WriteFile(path, data, 0o644)
}

func tryTool(k *kb, m *model, tool, change string) []returnedValue {
	script := firstString(m, "runs", tool)
	place := firstString(m, "reads", tool)
	if !inFolder(script) {
		return nil
	}
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	folder := filepath.Join(dir, "folder")
	if err := copyFolder(".", folder); err != nil {
		return nil
	}
	for _, add := range addedLines(k, m, change) {
		if !inFolder(add.file) {
			return nil
		}
		if err := appendLine(folder, add.file, add.line); err != nil {
			return nil
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", script)
	cmd.Dir = folder
	cmd.Env = append(os.Environ(), changeEnv+"="+change)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	cmd.Run()
	code := -1
	if cmd.ProcessState != nil {
		code = cmd.ProcessState.ExitCode()
	}
	out := []returnedValue{{"exit code", ast.Number(int64(code))}}
	var text string
	switch place {
	case stdoutPlace:
		text = stdout.String()
	case stderrPlace:
		text = stderr.String()
	default:
		return out
	}
	stmts, _ := parsePlain(place, text)
	seen := map[string]bool{}
	for _, s := range stmts {
		if s.bad || len(s.conds) > 0 || s.head.form != fVerb || len(s.head.args) != 2 {
			continue
		}
		ground := true
		for _, v := range s.head.args {
			if v.kind == vBlank {
				ground = false
			}
		}
		if !ground {
			continue
		}
		var v returnedValue
		switch s.head.phrase {
		case "breaks":
			v = returnedValue{"broke", pvalConst(s.head.args[1])}
		case "holds because":
			v = returnedValue{"explanation", ast.String(s.head.render(false))}
		default:
			continue
		}
		key := v.field + "\n" + v.value.String()
		if !seen[key] {
			seen[key] = true
			out = append(out, v)
		}
	}
	return out
}
