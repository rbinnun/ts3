package main

import (
	"bytes"
	"context"
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
	"time"

	"codeberg.org/TauCeti/mangle-go/ast"
	"mvdan.cc/sh/v3/syntax"
)

const (
	toolsFile = "tools.go"
	theFolder = "the folder"
	tryLimit  = 30 * time.Minute
)

var toolInstructions = map[string]int{
	"runs":          2,
	"reads":         2,
	"adds line":     3,
	"holds because": 2,
}

type result struct {
	field string
	value ast.Constant
}

type tool func(*machine, command) ([]result, error)

var toolbox = map[string]tool{
	"list":             list,
	"find go comments": findGoComments,
	"find sh comments": findShComments,
	"try":              try,
}

type outcome struct {
	results []result
	err     error
}

func (m *machine) useTools(batch []command) []error {
	outcomes := make([]outcome, len(batch))
	slots := make(chan struct{}, max(runtime.NumCPU(), 2))
	var wg sync.WaitGroup
	for i, c := range batch {
		use, ok := toolbox[c.tool]
		if !ok {
			if m.holds(fact("in the catalog", str(c.tool))) {
				outcomes[i].err = fmt.Errorf("%s has no tool called %s", toolsFile, c.tool)
			}
			continue
		}
		wg.Add(1)
		go func() {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			results, err := use(m, c)
			outcomes[i] = outcome{results: results, err: err}
		}()
	}
	wg.Wait()
	errs := make([]error, len(batch))
	for i, c := range batch {
		for _, r := range outcomes[i].results {
			m.create(toolsFile, fact("returned", str(c.name), str(r.field), r.value))
		}
		errs[i] = outcomes[i].err
	}
	return errs
}

func (m *machine) local(name string) (string, error) {
	if !filepath.IsLocal(name) {
		return "", fmt.Errorf("%s is not a file in the folder", name)
	}
	return filepath.Join(m.folder, filepath.FromSlash(name)), nil
}

func list(m *machine, c command) ([]result, error) {
	if c.input != theFolder {
		return nil, fmt.Errorf("%s can only list %s", c.tool, theFolder)
	}
	var out []result
	err := filepath.WalkDir(m.folder, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		rel, err := filepath.Rel(m.folder, path)
		if err != nil {
			return err
		}
		out = append(out, result{field: "file", value: ast.String(filepath.ToSlash(rel))})
		return nil
	})
	return out, err
}

func commentLines(text string) []result {
	var out []result
	for _, line := range strings.Split(text, "\n") {
		if line = strings.TrimSpace(line); line != "" {
			out = append(out, result{field: "comment", value: ast.String(line)})
		}
	}
	return out
}

func findGoComments(m *machine, c command) ([]result, error) {
	path, err := m.local(c.input)
	if err != nil {
		return nil, err
	}
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	files := token.NewFileSet()
	var s scanner.Scanner
	s.Init(files.AddFile(c.input, -1, len(src)), src, nil, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out, nil
		}
		if tok == token.COMMENT {
			out = append(out, commentLines(lit)...)
		}
	}
}

func findShComments(m *machine, c command) ([]result, error) {
	path, err := m.local(c.input)
	if err != nil {
		return nil, err
	}
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	parser := syntax.NewParser(syntax.KeepComments(true), syntax.Variant(syntax.LangPOSIX))
	file, err := parser.Parse(bytes.NewReader(src), c.input)
	if err != nil {
		return nil, err
	}
	var out []result
	syntax.Walk(file, func(n syntax.Node) bool {
		if note, ok := n.(*syntax.Comment); ok {
			out = append(out, commentLines("#"+note.Text)...)
		}
		return true
	})
	return out, nil
}

type addition struct {
	at   int
	file string
	line string
}

func (m *machine) additions(change string) []addition {
	var out []addition
	for _, row := range m.rows("adds line", 3) {
		if s, ok := text(row[0]); !ok || s != change {
			continue
		}
		at, ok := m.factAt[fact("adds line", row[0], row[1], row[2]).String()]
		if !ok {
			at = len(m.rules)
		}
		out = append(out, addition{at: at, file: valueText(row[1]), line: valueText(row[2])})
	}
	sort.SliceStable(out, func(i, j int) bool { return out[i].at < out[j].at })
	return out
}

func copyFolder(from, to string) error {
	return filepath.WalkDir(from, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(from, path)
		if err != nil {
			return err
		}
		target := filepath.Join(to, rel)
		switch {
		case d.IsDir():
			return os.MkdirAll(target, 0o755)
		case d.Type()&fs.ModeSymlink != 0:
			link, err := os.Readlink(path)
			if err != nil {
				return err
			}
			return os.Symlink(link, target)
		case d.Type().IsRegular():
			info, err := d.Info()
			if err != nil {
				return err
			}
			data, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			return os.WriteFile(target, data, info.Mode().Perm())
		}
		return nil
	})
}

func addLine(folder, name, line string) error {
	if !filepath.IsLocal(name) {
		return fmt.Errorf("%s is not a file in the folder", name)
	}
	path := filepath.Join(folder, filepath.FromSlash(name))
	old, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	mode := fs.FileMode(0o644)
	if info, err := os.Stat(path); err == nil {
		mode = info.Mode().Perm()
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, append(old, line+"\n"...), mode)
}

type said struct {
	line string
	lit  literal
}

func factsIn(output string) []said {
	chunks, _ := chunksOf(output)
	var out []said
	for _, c := range chunks {
		if len(c.lines) != 1 {
			continue
		}
		lit, err := lineLiteral(c.lines[0], false)
		if err != nil || !lit.ground() {
			continue
		}
		out = append(out, said{line: c.lines[0], lit: lit})
	}
	return out
}

func try(m *machine, c command) ([]result, error) {
	var runs []string
	for _, f := range m.about("runs", 2, c.tool) {
		name, ok := text(f)
		if !ok {
			return nil, fmt.Errorf("%s cannot run %s", c.tool, f.String())
		}
		runs = append(runs, name)
	}
	if len(runs) != 1 {
		return nil, fmt.Errorf("%s should run one file, and it runs %d", c.tool, len(runs))
	}
	places := m.about("reads", 2, c.tool)
	if len(places) == 0 {
		return nil, fmt.Errorf("%s reads nothing", c.tool)
	}
	for _, p := range places {
		if s, _ := text(p); s != standardOutput {
			return nil, fmt.Errorf("%s cannot read %s", c.tool, p.String())
		}
	}
	if !filepath.IsLocal(runs[0]) {
		return nil, fmt.Errorf("%s is not a file in the folder", runs[0])
	}
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(dir)
	if err := copyFolder(m.folder, dir); err != nil {
		return nil, err
	}
	for _, a := range m.additions(c.input) {
		if err := addLine(dir, a.file, a.line); err != nil {
			return nil, err
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), tryLimit)
	defer cancel()
	run := exec.CommandContext(ctx, "sh", filepath.FromSlash(runs[0]))
	run.Dir = dir
	run.Env = append(os.Environ(), changeSignal+"="+c.input)
	var out bytes.Buffer
	run.Stdout = &out
	err = run.Run()
	var exit *exec.ExitError
	if err != nil && !errors.As(err, &exit) {
		return nil, err
	}
	code := run.ProcessState.ExitCode()
	if code < 0 {
		return nil, fmt.Errorf("%s was stopped before it finished", runs[0])
	}
	results := []result{{field: "exit code", value: ast.Number(int64(code))}}
	for _, s := range factsIn(out.String()) {
		if len(s.lit.args) != 2 {
			continue
		}
		switch s.lit.name {
		case mangleName(lawVerb):
			results = append(results, result{field: "broke", value: s.lit.args[1].(ast.Constant)})
		case mangleName(reasonVerb):
			results = append(results, result{field: "why", value: ast.String(s.line)})
		}
	}
	return results, nil
}
