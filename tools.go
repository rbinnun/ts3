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
	"strings"
	"time"
)

const (
	tools      = "tools.go"
	trialKind  = "a change"
	trialLimit = 10 * time.Minute
)

type call struct {
	tool  term
	input term
}

type result struct {
	field string
	value term
}

func (r result) fact(command term) literal {
	return relation("returned", command, str(r.field), r.value)
}

func runTool(c call, k *knowledge) ([]result, error) {
	if c.tool.kind != stringTerm || c.input.kind != stringTerm {
		return nil, nil
	}
	switch c.tool.text {
	case "list":
		return list(c.input.text)
	case "find go comments":
		return findGoComments(c.input.text)
	case "find sh comments":
		return findShComments(c.input.text)
	case "try":
		return try(c.input.text, k)
	}
	return nil, nil
}

func list(place string) ([]result, error) {
	folder := place
	if place == "the folder" {
		folder = "."
	}
	entries, err := os.ReadDir(folder)
	if err != nil {
		return nil, err
	}
	var found []result
	for _, e := range entries {
		found = append(found, result{"file", str(e.Name())})
	}
	return found, nil
}

func oneLine(text string) string {
	return strings.Join(strings.Fields(text), " ")
}

func findGoComments(name string) ([]result, error) {
	src, err := os.ReadFile(name)
	if err != nil {
		return nil, err
	}
	var s scanner.Scanner
	s.Init(token.NewFileSet().AddFile(name, -1, len(src)), src, nil, scanner.ScanComments)
	var found []result
	for {
		_, tok, text := s.Scan()
		if tok == token.EOF {
			return found, nil
		}
		if tok == token.COMMENT {
			found = append(found, result{"comment", str(oneLine(text))})
		}
	}
}

func findShComments(name string) ([]result, error) {
	src, err := os.ReadFile(name)
	if err != nil {
		return nil, err
	}
	var found []result
	var quote byte
	wordStart := true
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case quote == '\'':
			if c == '\'' {
				quote = 0
			}
		case quote == '"':
			if c == '\\' {
				i++
			} else if c == '"' {
				quote = 0
			}
		case c == '\\':
			i++
			wordStart = false
		case c == '\'' || c == '"':
			quote = c
			wordStart = false
		case c == '#' && wordStart:
			end := bytes.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			found = append(found, result{"comment", str(oneLine(string(src[i : i+end])))})
			i += end - 1
		default:
			wordStart = strings.IndexByte(" \t\n;&|()", c) >= 0
		}
	}
	return found, nil
}

func copyFolder(to string) error {
	return filepath.WalkDir(".", func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		target := filepath.Join(to, path)
		if d.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		if !d.Type().IsRegular() {
			return nil
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		return os.WriteFile(target, data, info.Mode().Perm())
	})
}

func appendLine(name, line string) error {
	if err := os.MkdirAll(filepath.Dir(name), 0o755); err != nil {
		return err
	}
	old, err := os.ReadFile(name)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	return os.WriteFile(name, append(old, line+"\n"...), 0o644)
}

func try(change string, k *knowledge) ([]result, error) {
	if k.m.kind != "" {
		return nil, fmt.Errorf("a change cannot be tried while this run is %s", k.m.kind)
	}
	run, place := "", ""
	for _, f := range k.ask(tools, "[tool] runs [file]") {
		if f[0] == str("try") {
			run = textOf(f[1])
		}
	}
	for _, f := range k.ask(tools, "[tool] reads [place]") {
		if f[0] == str("try") {
			place = textOf(f[1])
		}
	}
	if run == "" {
		return nil, fmt.Errorf("try has nothing to run")
	}
	dir, err := os.MkdirTemp("", "try")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(dir)
	if err := copyFolder(dir); err != nil {
		return nil, err
	}
	for _, f := range k.ask(tools, "[change] adds line [file] [line]") {
		if f[0] != str(change) {
			continue
		}
		if !filepath.IsLocal(textOf(f[1])) {
			return nil, fmt.Errorf("%s is outside the folder", textOf(f[1]))
		}
		if err := appendLine(filepath.Join(dir, textOf(f[1])), textOf(f[2])); err != nil {
			return nil, err
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), trialLimit)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", run, trialKind)
	cmd.Dir = dir
	var out bytes.Buffer
	if place == "standard output" {
		cmd.Stdout = &out
	}
	var exit *exec.ExitError
	if err := cmd.Run(); err != nil && !errors.As(err, &exit) {
		return nil, err
	}
	if ctx.Err() != nil {
		return nil, fmt.Errorf("trying %s took too long", change)
	}
	found := []result{{"exit code", num(int64(cmd.ProcessState.ExitCode()))}}
	for _, line := range strings.Split(out.String(), "\n") {
		if line == "" || line[0] == ' ' {
			continue
		}
		l, err := readLiteral(line)
		if err != nil || l.shape != relationShape || l.word != "breaks" || len(l.args) != 2 || !l.ground() {
			continue
		}
		found = append(found, result{"broke", l.args[1]}, result{"why", str(line)})
	}
	return found, nil
}
