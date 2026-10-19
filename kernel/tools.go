package main

import (
	"bytes"
	"go/scanner"
	"go/token"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"

	"github.com/google/mangle/ast"
)

type result struct {
	field string
	value ast.Constant
}

type addedLine struct {
	file  string
	line  string
	order int
	text  string
}

type trial struct {
	change string
	level  string
	script string
	lines  []addedLine
}

func (m *machine) runCalls(calls []call) {
	jobs := make([]func() []result, len(calls))
	for i, c := range calls {
		jobs[i] = m.tool(c)
	}
	results := make([][]result, len(calls))
	slots := make(chan struct{}, runtime.NumCPU())
	var wg sync.WaitGroup
	for i := range jobs {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			results[i] = jobs[i]()
		}(i)
	}
	wg.Wait()
	for i, c := range calls {
		m.ran[c.key] = true
		for _, r := range results[i] {
			m.addToolFact(c.command, r.field, r.value)
		}
	}
}

func (m *machine) tool(c call) func() []result {
	switch c.tool {
	case "list":
		return func() []result { return m.list(c.input) }
	case "find go comments":
		return func() []result { return m.goComments(c.input) }
	case "find sh comments":
		return func() []result { return m.shComments(c.input) }
	case "try":
		t := m.plan(c.input)
		return func() []result { return m.try(t) }
	}
	return func() []result { return nil }
}

func (m *machine) list(input string) []result {
	dir := m.folder
	if input != "the folder" {
		dir = filepath.Join(m.folder, input)
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var out []result
	for _, e := range entries {
		if e.Type().IsRegular() {
			out = append(out, result{"file", ast.String(e.Name())})
		}
	}
	return out
}

func (m *machine) goComments(input string) []result {
	src, err := os.ReadFile(filepath.Join(m.folder, input))
	if err != nil {
		return nil
	}
	fset := token.NewFileSet()
	file := fset.AddFile(input, fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, func(token.Position, string) {}, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, result{"comment", ast.String(lit)})
		}
	}
}

func (m *machine) shComments(input string) []result {
	src, err := os.ReadFile(filepath.Join(m.folder, input))
	if err != nil {
		return nil
	}
	var out []result
	single, double := false, false
	prev := byte('\n')
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case single:
			if c == '\'' {
				single = false
			}
		case double:
			if c == '\\' && i+1 < len(src) {
				i++
				c = src[i]
			} else if c == '"' {
				double = false
			}
		case c == '\\' && i+1 < len(src):
			i++
			c = src[i]
		case c == '\'':
			single = true
		case c == '"':
			double = true
		case c == '#' && strings.IndexByte("\n \t;&|()", prev) >= 0:
			j := bytes.IndexByte(src[i:], '\n')
			if j < 0 {
				j = len(src) - i
			}
			out = append(out, result{"comment", ast.String(strings.TrimRight(string(src[i:i+j]), "\r"))})
			i += j - 1
			c = '#'
		}
		prev = c
	}
	return out
}

func (m *machine) plan(change string) trial {
	t := trial{change: change, level: m.level, script: "runme.sh"}
	for _, row := range m.facts("runs", 2) {
		if textOf(row[0]) == "try" {
			t.script = textOf(row[1])
		}
	}
	order := map[string]int{}
	levels := map[string]string{}
	for i, r := range m.rules {
		if r.fact("adds line", 3) {
			k := formatAtom(r.head)
			if _, ok := order[k]; !ok {
				order[k] = i
				levels[k] = r.level
			}
		}
	}
	for _, row := range m.facts("adds line", 3) {
		if textOf(row[0]) != change {
			continue
		}
		a := atom{pred: "adds line", args: []value{valueOf(row[0]), valueOf(row[1]), valueOf(row[2])}}
		k := formatAtom(a)
		o, ok := order[k]
		if !ok {
			o = len(m.rules)
		}
		t.lines = append(t.lines, addedLine{file: textOf(row[1]), line: textOf(row[2]), order: o, text: k})
	}
	sort.SliceStable(t.lines, func(i, j int) bool {
		if t.lines[i].order != t.lines[j].order {
			return t.lines[i].order < t.lines[j].order
		}
		return t.lines[i].text < t.lines[j].text
	})
	if len(t.lines) > 0 {
		if l, ok := levels[t.lines[0].text]; ok {
			t.level = l
		}
	}
	return t
}

func copyFile(from, to string) error {
	data, err := os.ReadFile(from)
	if err != nil {
		return err
	}
	return os.WriteFile(to, data, 0o644)
}

func copyDir(from, to string) error {
	if err := os.MkdirAll(to, 0o755); err != nil {
		return err
	}
	entries, err := os.ReadDir(from)
	if err != nil {
		return err
	}
	for _, e := range entries {
		src, dst := filepath.Join(from, e.Name()), filepath.Join(to, e.Name())
		switch {
		case e.IsDir():
			if err := copyDir(src, dst); err != nil {
				return err
			}
		case e.Type().IsRegular():
			if err := copyFile(src, dst); err != nil {
				return err
			}
		}
	}
	return nil
}

func (m *machine) copyLevels(to string) error {
	entries, err := os.ReadDir(m.root)
	if err != nil {
		return err
	}
	for _, e := range entries {
		src, dst := filepath.Join(m.root, e.Name()), filepath.Join(to, e.Name())
		switch {
		case e.IsDir() && exists(filepath.Join(src, e.Name()+".plain")):
			if err := copyDir(src, dst); err != nil {
				return err
			}
		case e.Type().IsRegular() && strings.HasSuffix(e.Name(), ".db"):
			if err := copyFile(src, dst); err != nil {
				return err
			}
		}
	}
	return nil
}

func appendLine(path, line string) error {
	data, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line...)
	data = append(data, '\n')
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, data, 0o644)
}

func (m *machine) try(t trial) []result {
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	if err := m.copyLevels(dir); err != nil {
		return nil
	}
	for _, l := range t.lines {
		if err := appendLine(filepath.Join(dir, t.level, l.file), l.line); err != nil {
			return nil
		}
	}
	cmd := exec.Command("sh", filepath.Join(dir, filepath.Base(m.kernelDir), t.script))
	cmd.Dir = filepath.Join(dir, t.level)
	cmd.Env = append(os.Environ(), changeVariable+"="+t.change)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = io.Discard
	code := 0
	if err := cmd.Run(); err != nil {
		e, ok := err.(*exec.ExitError)
		if !ok {
			return nil
		}
		code = e.ExitCode()
	}
	res := []result{{"exit code", ast.Number(int64(code))}}
	for _, line := range strings.Split(out.String(), "\n") {
		a, err := parseAtom(line)
		if err != nil {
			continue
		}
		switch a.key() {
		case "breaks/2":
			res = append(res, result{"broke", constOf(a.args[1])})
		case "holds because/2":
			res = append(res, result{"explanation", ast.String(line)})
		}
	}
	return res
}
