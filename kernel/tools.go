package main

import (
	"bytes"
	"errors"
	"fmt"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
)

const (
	listTool     = "list"
	commentsTool = "find go comments"
	tryTool      = "try"
)

type call struct {
	command term
	tool    string
	input   term
}

func (c call) key() string {
	return atom{name: "calls", args: []term{c.command, textOf(c.tool), c.input}}.line()
}

type result struct {
	field string
	value term
}

func (s *session) pendingCalls(k *knowledge) []call {
	var calls []call
	for _, a := range k.all("calls", 3) {
		c := call{command: a.args[0], tool: a.args[1].plain(), input: a.args[2]}
		if !s.called[c.key()] {
			calls = append(calls, c)
		}
	}
	return calls
}

func (s *session) runTools(k *knowledge, calls []call) {
	results := make([][]result, len(calls))
	slots := make(chan struct{}, runtime.NumCPU())
	var wait sync.WaitGroup
	for i, c := range calls {
		s.called[c.key()] = true
		wait.Add(1)
		go func(i int, c call) {
			defer wait.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			found, err := s.use(k, c)
			if err != nil {
				s.problem(fmt.Sprintf("%s cannot use %s on %s: %v", c.command.plain(), c.tool, c.input.plain(), err))
			}
			results[i] = found
		}(i, c)
	}
	wait.Wait()
	for i, c := range calls {
		for _, r := range results[i] {
			s.observe(atom{name: "returned", args: []term{c.command, textOf(r.field), r.value}}, toolsFile)
		}
	}
}

func (s *session) use(k *knowledge, c call) ([]result, error) {
	switch c.tool {
	case listTool:
		return s.list(c.input.plain())
	case commentsTool:
		return s.findGoComments(c.input.plain())
	case tryTool:
		return s.try(k, c.input)
	}
	return nil, nil
}

func (s *session) list(input string) ([]result, error) {
	directory := s.levelDir
	if input != theFolder {
		name, ok := fileName(input)
		if !ok {
			return nil, fmt.Errorf("%s is not a folder name", input)
		}
		directory = s.path(name)
	}
	var found []result
	err := filepath.WalkDir(directory, func(file string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.IsDir() {
			return nil
		}
		relative, err := filepath.Rel(s.root, file)
		if err != nil {
			return err
		}
		found = append(found, result{"file", textOf(filepath.ToSlash(relative))})
		return nil
	})
	return found, err
}

func (s *session) findGoComments(input string) ([]result, error) {
	name, ok := fileName(input)
	if !ok {
		return nil, fmt.Errorf("%s is not a file name", input)
	}
	source, err := os.ReadFile(s.path(name))
	if err != nil {
		return nil, err
	}
	files := token.NewFileSet()
	file := files.AddFile(name, files.Base(), len(source))
	var reader scanner.Scanner
	reader.Init(file, source, nil, scanner.ScanComments)
	var found []result
	for {
		_, kind, literal := reader.Scan()
		if kind == token.EOF {
			return found, nil
		}
		if kind == token.COMMENT {
			text := strings.Join(strings.Fields(strings.ReplaceAll(literal, "\r", "")), " ")
			found = append(found, result{"comment", textOf(text)})
		}
	}
}

type addition struct {
	file string
	line string
}

func (s *session) additions(k *knowledge, change term) []addition {
	order := map[string]int{}
	for i, r := range s.rules {
		if len(r.conditions) == 0 {
			if _, ok := order[r.head.line()]; !ok {
				order[r.head.line()] = i
			}
		}
	}
	var facts []atom
	for _, a := range k.all("adds line", 3) {
		if a.args[0] == change {
			facts = append(facts, a)
		}
	}
	rank := func(a atom) int {
		if i, ok := order[a.line()]; ok {
			return i
		}
		return len(s.rules)
	}
	sort.SliceStable(facts, func(i, j int) bool { return rank(facts[i]) < rank(facts[j]) })
	var found []addition
	for _, a := range facts {
		found = append(found, addition{a.args[1].plain(), a.args[2].plain()})
	}
	return found
}

func copyFolder(from, to string) error {
	return filepath.WalkDir(from, func(file string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		relative, err := filepath.Rel(from, file)
		if err != nil {
			return err
		}
		target := filepath.Join(to, relative)
		if entry.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		content, err := os.ReadFile(file)
		if err != nil {
			return err
		}
		return os.WriteFile(target, content, 0o644)
	})
}

func appendLine(root, file, line string) error {
	name, ok := fileName(file)
	if !ok {
		return fmt.Errorf("%s is not a file name", file)
	}
	target := filepath.Join(root, filepath.FromSlash(name))
	if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
		return err
	}
	existing, err := os.ReadFile(target)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(existing) > 0 && existing[len(existing)-1] != '\n' {
		line = "\n" + line
	}
	opened, err := os.OpenFile(target, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	if _, err := opened.WriteString(line + "\n"); err != nil {
		opened.Close()
		return err
	}
	return opened.Close()
}

func (s *session) copiedLevels() []string {
	levels := []string{s.level, levelOf(engineFile)}
	for _, f := range s.files {
		levels = append(levels, levelOf(f.name))
	}
	for _, a := range s.stated("builds on", 2) {
		levels = append(levels, a.args[1].plain())
	}
	seen := map[string]bool{}
	var found []string
	for _, level := range levels {
		if level == "" || seen[level] || strings.ContainsAny(level, `/\`) || level == "." || level == ".." {
			continue
		}
		seen[level] = true
		found = append(found, level)
	}
	return found
}

func (s *session) try(k *knowledge, change term) ([]result, error) {
	work, err := os.MkdirTemp("", "plain-change-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(work)
	for _, level := range s.copiedLevels() {
		if info, err := os.Stat(filepath.Join(s.root, level)); err != nil || !info.IsDir() {
			continue
		}
		if err := copyFolder(filepath.Join(s.root, level), filepath.Join(work, level)); err != nil {
			return nil, err
		}
		if content, err := os.ReadFile(filepath.Join(s.root, level+".db")); err == nil {
			if err := os.WriteFile(filepath.Join(work, level+".db"), content, 0o644); err != nil {
				return nil, err
			}
		}
	}
	if err := os.MkdirAll(filepath.Join(work, s.level), 0o755); err != nil {
		return nil, err
	}
	for _, a := range s.additions(k, change) {
		if err := appendLine(work, a.file, a.line); err != nil {
			return nil, err
		}
	}
	executable, err := os.Executable()
	if err != nil {
		return nil, err
	}
	command := exec.Command(executable, changeArgument)
	command.Dir = filepath.Join(work, s.level)
	var output bytes.Buffer
	command.Stdout = &output
	code := 0
	if err := command.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return nil, err
		}
		code = exit.ExitCode()
	}
	found := []result{{"exit code", numberOf(int64(code))}}
	for _, line := range strings.Split(output.String(), "\n") {
		a, err := parseFact(line)
		if err != nil || len(a.args) != 2 {
			continue
		}
		switch a.name {
		case "breaks":
			found = append(found, result{"broke", a.args[1]})
		case "holds because":
			found = append(found, result{"explanation", textOf(a.line())})
		}
	}
	return found, nil
}
