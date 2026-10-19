package main

import (
	"bytes"
	"go/scanner"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
)

const (
	toolsFile       = "tools.go"
	returnedPattern = "[command] returned [field] [value]"
	standardOutput  = "standard output"
)

var toolsInstructions = []string{
	"[tool] runs [file]",
	"[tool] reads [place]",
	"[change] adds line [file] [line]",
	"[fact] holds because [reason]",
}

var commentLanguages = map[string]string{
	"find go comments": "go",
	"find sh comments": "sh",
}

type call struct {
	command term
	tool    string
	input   term
}

type result struct {
	field string
	value term
}

func (c call) job() string {
	return c.tool + "\x00" + c.input.plain()
}

func (m *machine) work(k *view) bool {
	calls, ok := m.instruction(engineFile, "[command] calls [tool] [input]")
	returned, ok2 := m.creates(toolsFile, returnedPattern)
	if !ok || !ok2 {
		return false
	}
	var todo []call
	for _, f := range k.facts(calls) {
		if f[1].kind != textTerm {
			continue
		}
		c := call{f[0], f[1].text, f[2]}
		key := c.command.plain() + "\x00" + c.job()
		if m.done[key] {
			continue
		}
		m.done[key] = true
		todo = append(todo, c)
	}
	if len(todo) == 0 {
		return false
	}
	var jobs []call
	planned := map[string]bool{}
	for _, c := range todo {
		if _, ok := m.cache[c.job()]; !ok && !planned[c.job()] {
			planned[c.job()] = true
			jobs = append(jobs, c)
		}
	}
	found := make([][]result, len(jobs))
	limit := make(chan bool, runtime.NumCPU())
	var wg sync.WaitGroup
	for i, c := range jobs {
		wg.Add(1)
		go func(i int, c call) {
			defer wg.Done()
			limit <- true
			defer func() { <-limit }()
			found[i] = m.use(c.tool, c.input, k)
		}(i, c)
	}
	wg.Wait()
	for i, c := range jobs {
		m.cache[c.job()] = found[i]
	}
	for _, c := range todo {
		for _, r := range m.cache[c.job()] {
			m.returned = append(m.returned, atom{returned, []term{c.command, text(r.field), r.value}})
		}
	}
	return true
}

func (m *machine) use(tool string, input term, k *view) []result {
	switch tool {
	case "list":
		return m.list()
	case "try":
		return m.try(input, k)
	}
	if language, ok := commentLanguages[tool]; ok {
		return m.comments(language, input)
	}
	return nil
}

func (m *machine) list() []result {
	entries, err := os.ReadDir(m.folder)
	if err != nil {
		return nil
	}
	var out []result
	for _, e := range entries {
		out = append(out, result{"file", text(e.Name())})
	}
	return out
}

func (m *machine) comments(language string, input term) []result {
	if input.kind != textTerm {
		return nil
	}
	data, err := os.ReadFile(filepath.Join(m.folder, input.text))
	if err != nil {
		return nil
	}
	var found []string
	switch language {
	case "go":
		found = goComments(data)
	case "sh":
		found = shComments(string(data))
	}
	var out []result
	for _, c := range found {
		out = append(out, result{"comment", text(c)})
	}
	return out
}

func goComments(src []byte) []string {
	fset := token.NewFileSet()
	file := fset.AddFile("", fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, func(token.Position, string) {}, scanner.ScanComments)
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

func shComments(src string) []string {
	var out []string
	single, double, start := false, false, true
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case single:
			single = c != '\''
			start = false
			continue
		case double:
			if c == '\\' {
				i++
			} else {
				double = c != '"'
			}
			start = false
			continue
		case c == '\\':
			i++
			start = false
			continue
		case c == '\'':
			single = true
		case c == '"':
			double = true
		case c == '#' && start:
			end := strings.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			out = append(out, src[i:i+end])
			i += end - 1
			start = true
			continue
		}
		start = strings.IndexByte(" \t\n;&|()<>", c) >= 0
	}
	return out
}

func (m *machine) try(change term, k *view) []result {
	runs, ok1 := m.instruction(toolsFile, "[tool] runs [file]")
	reads, ok2 := m.instruction(toolsFile, "[tool] reads [place]")
	adds, ok3 := m.instruction(toolsFile, "[change] adds line [file] [line]")
	because, ok4 := m.instruction(toolsFile, "[fact] holds because [reason]")
	if m.isChange || change.kind != textTerm || !ok1 || !ok2 || !ok3 || !ok4 {
		return nil
	}
	script, place := "", ""
	for _, f := range k.facts(runs) {
		if f[0] == text("try") {
			script = f[1].raw()
		}
	}
	for _, f := range k.facts(reads) {
		if f[0] == text("try") {
			place = f[1].raw()
		}
	}
	if script == "" || place != standardOutput {
		return nil
	}
	type addition struct {
		file, line string
		order, at  int
	}
	var additions []addition
	for _, f := range k.facts(adds) {
		if f[0] == change {
			order, at := m.position(atom{adds, f})
			additions = append(additions, addition{f[1].raw(), f[2].raw(), order, at})
		}
	}
	sort.SliceStable(additions, func(i, j int) bool {
		if additions[i].order != additions[j].order {
			return additions[i].order < additions[j].order
		}
		return additions[i].at < additions[j].at
	})
	tmp, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(tmp)
	dst := filepath.Join(tmp, filepath.Base(m.folder))
	if err := copyFolder(m.folder, dst); err != nil {
		return nil
	}
	for _, a := range additions {
		if err := addLine(filepath.Join(dst, a.file), a.line); err != nil {
			return nil
		}
	}
	cmd := exec.Command("sh", script, change.text)
	cmd.Dir = dst
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = os.Stderr
	cmd.Run()
	if cmd.ProcessState == nil {
		return nil
	}
	results := []result{{"exit code", number(int64(cmd.ProcessState.ExitCode()))}}
	breaks := pred{relation, "breaks", 2}
	for _, line := range strings.Split(out.String(), "\n") {
		a, err := readAtom(line)
		if err != nil || line == "" {
			continue
		}
		switch a.pred.id() {
		case breaks.id():
			results = append(results, result{"broke", a.args[1]})
		case because.id():
			results = append(results, result{"explanation", text(line)})
		}
	}
	return results
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
		data, err := os.ReadFile(filepath.Join(from, e.Name()))
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(to, e.Name()), data, 0o644); err != nil {
			return err
		}
	}
	return nil
}

func addLine(path, line string) error {
	old, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	return os.WriteFile(path, append(old, []byte(line+"\n")...), 0o644)
}
