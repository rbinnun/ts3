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
	"strings"
	"sync"
	"time"
)

var toolsDo = set("runs/2", "reads/2", "adds line/3", "holds because/2")

var toolsMake = set("returned/3")

var toolbox = map[string]func(string, val, *world) []result{
	"list":             list,
	"find go comments": goComments,
	"find sh comments": shComments,
	"try":              try,
}

func toolsName() string {
	_, file, _, _ := runtime.Caller(0)
	return filepath.Base(file)
}

func (s *state) runJobs(w *world) bool {
	if s.instr["uses/3"] == "" {
		return false
	}
	var todo []job
	for _, row := range w.facts("uses", 3) {
		j := job{row[0], row[1].text(), row[2]}
		if _, done := s.results[j]; !done && !row[1].num {
			todo = append(todo, j)
			s.results[j] = nil
		}
	}
	if len(todo) == 0 {
		return false
	}
	var mu sync.Mutex
	var wg sync.WaitGroup
	slots := make(chan struct{}, runtime.NumCPU())
	for _, j := range todo {
		wg.Add(1)
		go func(j job) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			tool := toolbox[j.tool]
			if tool == nil {
				return
			}
			found := tool(j.tool, j.input, w)
			mu.Lock()
			s.results[j] = found
			mu.Unlock()
		}(j)
	}
	wg.Wait()
	return true
}

func inFolder(name string) bool {
	return name != "" && name != "." && name != ".." && filepath.Base(name) == name
}

func list(name string, input val, w *world) []result {
	entries, err := os.ReadDir(".")
	if err != nil {
		return nil
	}
	var out []result
	for _, e := range entries {
		if e.Type().IsRegular() {
			out = append(out, result{"file", str(e.Name())})
		}
	}
	return out
}

func goComments(name string, input val, w *world) []result {
	if input.num || !inFolder(input.s) {
		return nil
	}
	src, err := os.ReadFile(input.s)
	if err != nil {
		return nil
	}
	var sc scanner.Scanner
	sc.Init(token.NewFileSet().AddFile(input.s, -1, len(src)), src, nil, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := sc.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, result{"comment", str(lit)})
		}
	}
}

func shComments(name string, input val, w *world) []result {
	if input.num || !inFolder(input.s) {
		return nil
	}
	data, err := os.ReadFile(input.s)
	if err != nil {
		return nil
	}
	src := string(data)
	var out []result
	var quoted byte
	start := true
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case quoted != 0:
			if c == '\\' && quoted == '"' {
				i++
			} else if c == quoted {
				quoted = 0
			}
			start = false
		case c == '\\':
			i++
			start = false
		case c == '\'' || c == '"':
			quoted = c
			start = false
		case c == '#' && start:
			end := strings.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			out = append(out, result{"comment", str(src[i : i+end])})
			i += end - 1
			start = false
		default:
			start = strings.IndexByte(" \t\n;&|()", c) >= 0
		}
	}
	return out
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

func addLine(path, line string) error {
	data, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(append(data, line...), '\n')
	return os.WriteFile(path, data, 0o644)
}

func try(name string, change val, w *world) []result {
	s := w.st
	if s.tinstr["runs/2"] == "" {
		return nil
	}
	runs := w.about("runs", name)
	if len(runs) != 1 || runs[0].num || !inFolder(runs[0].s) {
		return nil
	}
	dir, err := os.MkdirTemp("", "change-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	if copyFolder(dir) != nil {
		return nil
	}
	if s.tinstr["adds line/3"] != "" {
		for _, row := range w.facts("adds line", 3) {
			if row[0] != change || row[1].num || !inFolder(row[1].s) {
				continue
			}
			if addLine(filepath.Join(dir, row[1].s), row[2].text()) != nil {
				return nil
			}
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", runs[0].s)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), changeEnv+"="+change.text())
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	cmd.Run()
	if cmd.ProcessState == nil {
		return nil
	}
	out := []result{{"exit code", num(int64(cmd.ProcessState.ExitCode()))}}
	if s.tinstr["reads/2"] == "" {
		return out
	}
	for _, place := range w.about("reads", name) {
		text := map[string]string{"standard output": stdout.String(), "standard error": stderr.String()}[place.text()]
		clauses, _ := parseFile(place.text(), text)
		for _, c := range clauses {
			if c.bad || len(c.body) > 0 || !c.head.ground() {
				continue
			}
			switch c.head.key() {
			case lawWord + "/2":
				out = append(out, result{"broke", c.head.args[1].v})
			case "holds because/2":
				if s.tinstr["holds because/2"] != "" {
					out = append(out, result{"why", str(c.head.text())})
				}
			}
		}
	}
	return out
}
