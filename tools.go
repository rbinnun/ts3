package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/scanner"
	"go/token"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

const (
	changeVariable = "THIS_RUN_IS_A_CHANGE"
	tryTimeout     = 20 * time.Minute
)

type toolResult struct {
	field string
	text  string
	num   int64
	isNum bool
}

type knowledge func(predicate string) [][]string

func runTool(tool, input string, know knowledge) ([]toolResult, error) {
	switch tool {
	case "list":
		return list(input)
	case "find go comments":
		return findGoComments(input)
	case "find sh comments":
		return findShComments(input)
	case "try":
		return try(input, know)
	}
	return nil, nil
}

func folderPath(input string) string {
	if input == theFolder {
		return "."
	}
	return input
}

func list(input string) ([]toolResult, error) {
	entries, err := os.ReadDir(folderPath(input))
	if err != nil {
		return nil, err
	}
	var out []toolResult
	for _, e := range entries {
		if e.Type().IsRegular() {
			out = append(out, toolResult{field: "file", text: e.Name()})
		}
	}
	return out, nil
}

func findGoComments(file string) ([]toolResult, error) {
	src, err := os.ReadFile(file)
	if err != nil {
		return nil, err
	}
	fset := token.NewFileSet()
	var s scanner.Scanner
	s.Init(fset.AddFile(file, fset.Base(), len(src)), src, nil, scanner.ScanComments)
	var out []toolResult
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out, nil
		}
		if tok == token.COMMENT {
			out = append(out, toolResult{field: "comment", text: lit})
		}
	}
}

func findShComments(file string) ([]toolResult, error) {
	src, err := os.ReadFile(file)
	if err != nil {
		return nil, err
	}
	var out []toolResult
	single, double := false, false
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case single:
			single = c != '\''
		case c == '\\':
			i++
		case double:
			double = c != '"'
		case c == '\'':
			single = true
		case c == '"':
			double = true
		case c == '#' && (i == 0 || bytes.IndexByte([]byte(" \t\n;&|()<>"), src[i-1]) >= 0):
			end := bytes.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			out = append(out, toolResult{field: "comment", text: string(src[i : i+end])})
			i += end
		}
	}
	return out, nil
}

func firstOf(know knowledge, predicate, subject string) string {
	for _, row := range know(predicate) {
		if len(row) == 2 && row[0] == subject {
			return row[1]
		}
	}
	return ""
}

func try(change string, know knowledge) ([]toolResult, error) {
	program := firstOf(know, "runs", "try")
	if program == "" {
		return nil, errors.New("nothing says what try runs")
	}
	if place := firstOf(know, "reads", "try"); place != "standard output" {
		return nil, fmt.Errorf("try can't read %q", place)
	}
	dir, err := os.MkdirTemp("", "change-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(dir)
	if err := copyFolder(".", dir); err != nil {
		return nil, err
	}
	for _, row := range know("adds line") {
		if len(row) == 3 && row[0] == change {
			if err := addLine(dir, row[1], row[2]); err != nil {
				return nil, err
			}
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), tryTimeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", program)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), changeVariable+"="+change)
	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = io.Discard
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return nil, err
		}
		code = exit.ExitCode()
	}
	out := []toolResult{{field: "exit code", num: int64(code), isNum: true}}
	laws, explanations := readView(stdout.String())
	for _, l := range laws {
		out = append(out, toolResult{field: "broke", text: l})
	}
	for _, e := range explanations {
		out = append(out, toolResult{field: "explanation", text: e})
	}
	return out, nil
}

func readView(text string) ([]string, []string) {
	var laws, explanations []string
	seen := map[string]bool{}
	raws, _ := splitStatements(text)
	for _, r := range raws {
		if len(r.lines) != 1 || r.problem != "" {
			continue
		}
		a, err := parseAtom(r.lines[0])
		if err != nil || !ground(a) {
			continue
		}
		switch {
		case a.verb == "breaks" && len(a.args) >= 2:
			if law := a.args[len(a.args)-1].text; !seen["broke "+law] {
				seen["broke "+law] = true
				laws = append(laws, law)
			}
		case a.verb == "holds because" && len(a.args) == 2:
			if e := a.args[0].text + " because " + a.args[1].text; !seen["explanation "+e] {
				seen["explanation "+e] = true
				explanations = append(explanations, e)
			}
		}
	}
	return laws, explanations
}

func ground(a atom) bool {
	for _, v := range a.args {
		if v.kind != textValue {
			return false
		}
	}
	return true
}

func copyFolder(from, to string) error {
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

func addLine(dir, file, line string) error {
	path := filepath.Join(dir, file)
	if rel, err := filepath.Rel(dir, path); err != nil || rel == "." || strings.HasPrefix(rel, "..") {
		return fmt.Errorf("%s is not in the folder", file)
	}
	old, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	return os.WriteFile(path, append(old, line+"\n"...), 0o644)
}
