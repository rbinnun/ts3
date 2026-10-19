package main

import (
	"bytes"
	"errors"
	"go/scanner"
	"go/token"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"mvdan.cc/sh/v3/syntax"
)

const toolsFile = "tools.go"

type call struct {
	command term
	tool    term
	input   term
}

type result struct {
	field string
	value term
}

var catalog = map[string]func(term, *knowledge) []result{
	"list":             list,
	"find go comments": findGoComments,
	"find sh comments": findShComments,
	"try":              try,
}

func runCommand(c call, k *knowledge) []atom {
	tool, ok := catalog[c.tool.value()]
	if !ok {
		return nil
	}
	var out []atom
	for _, r := range tool(c.input, k) {
		out = append(out, fact("returned", c.command, word(r.field), r.value))
	}
	return out
}

func folderOf(input term) string {
	if input.value() == "the folder" {
		return "."
	}
	return input.value()
}

func list(input term, _ *knowledge) []result {
	entries, err := os.ReadDir(folderOf(input))
	if err != nil {
		return nil
	}
	var out []result
	for _, e := range entries {
		if !e.IsDir() {
			out = append(out, result{"file", plainValue(e.Name())})
		}
	}
	return out
}

func findGoComments(input term, _ *knowledge) []result {
	src, err := os.ReadFile(input.value())
	if err != nil {
		return nil
	}
	file := token.NewFileSet().AddFile(input.value(), -1, len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, result{"comment", word(lit)})
		}
	}
}

func findShComments(input term, _ *knowledge) []result {
	src, err := os.ReadFile(input.value())
	if err != nil {
		return nil
	}
	var out []result
	f, err := syntax.NewParser(syntax.KeepComments(true)).Parse(bytes.NewReader(src), input.value())
	if err != nil {
		for _, line := range strings.Split(string(src), "\n") {
			if text := strings.TrimSpace(line); strings.HasPrefix(text, "#") {
				out = append(out, result{"comment", word(text)})
			}
		}
		return out
	}
	syntax.Walk(f, func(n syntax.Node) bool {
		if c, ok := n.(*syntax.Comment); ok {
			out = append(out, result{"comment", word("#" + c.Text)})
		}
		return true
	})
	return out
}

func try(input term, k *knowledge) []result {
	if os.Getenv(changeVariable) != "" {
		return nil
	}
	scripts := k.values("runs", "try")
	if len(scripts) != 1 {
		return nil
	}
	base, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(base)
	dir := filepath.Join(base, "folder")
	if err := copyFolder(".", dir); err != nil {
		return nil
	}
	for _, args := range k.facts("adds_line", 3) {
		name := args[1].value()
		if args[0].plain() != input.plain() || filepath.Base(name) != name {
			continue
		}
		if err := appendLine(filepath.Join(dir, name), args[2].value()); err != nil {
			return nil
		}
	}
	cmd := exec.Command("sh", scripts[0])
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), changeVariable+"="+input.value())
	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = os.Stderr
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return nil
		}
		code = exit.ExitCode()
	}
	out := []result{{"exit code", count(int64(code))}}
	for _, place := range k.values("reads", "try") {
		if place != "standard output" {
			continue
		}
		for _, line := range strings.Split(stdout.String(), "\n") {
			a, err := parseAtom(line)
			if err != nil || a.form.kind != relation || len(a.args) != 2 || !a.ground() {
				continue
			}
			switch a.form.words {
			case "breaks":
				out = append(out, result{"broke", a.args[1]})
			case "holds because":
				out = append(out, result{"explanation", word(a.plain())})
			}
		}
	}
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
		if e.IsDir() {
			continue
		}
		info, err := e.Info()
		if err != nil {
			return err
		}
		src, err := os.Open(filepath.Join(from, e.Name()))
		if err != nil {
			return err
		}
		dst, err := os.OpenFile(filepath.Join(to, e.Name()), os.O_CREATE|os.O_WRONLY|os.O_TRUNC, info.Mode().Perm())
		if err != nil {
			src.Close()
			return err
		}
		_, err = io.Copy(dst, src)
		src.Close()
		if closeErr := dst.Close(); err == nil {
			err = closeErr
		}
		if err != nil {
			return err
		}
	}
	return nil
}

func appendLine(path, line string) error {
	old, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	text := string(old)
	if text != "" && !strings.HasSuffix(text, "\n") {
		text += "\n"
	}
	return os.WriteFile(path, []byte(text+line+"\n"), 0o644)
}
