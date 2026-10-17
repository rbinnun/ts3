package main

import (
	"bytes"
	"context"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"time"

	"codeberg.org/TauCeti/mangle-go/ast"
)

const runLimit = 10 * time.Minute

type outcome struct {
	field string
	value ast.Constant
}

func useTool(k *knowledge, tool, input string) []outcome {
	switch tool {
	case "list":
		return listFolder(input)
	case "find go comments":
		return findGoComments(input)
	case "find sh comments":
		return findShComments(input)
	}
	if k.executes(toolsFile, "runs", 2) && len(k.objects("runs", tool)) > 0 {
		return tryChange(k, tool, input)
	}
	return nil
}

func folderPath(input string) (string, bool) {
	if input == "the folder" {
		return ".", true
	}
	return input, filepath.IsLocal(input)
}

func listFolder(input string) []outcome {
	dir, ok := folderPath(input)
	if !ok {
		return nil
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var out []outcome
	for _, e := range entries {
		out = append(out, outcome{"file", ast.String(e.Name())})
	}
	return out
}

func findGoComments(input string) []outcome {
	if !filepath.IsLocal(input) {
		return nil
	}
	src, err := os.ReadFile(input)
	if err != nil {
		return nil
	}
	files := token.NewFileSet()
	var s scanner.Scanner
	s.Init(files.AddFile(input, -1, len(src)), src, func(token.Position, string) {}, scanner.ScanComments)
	var out []outcome
	for {
		_, tok, text := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, outcome{"comment", ast.String(text)})
		}
	}
}

func findShComments(input string) []outcome {
	if !filepath.IsLocal(input) {
		return nil
	}
	src, err := os.ReadFile(input)
	if err != nil {
		return nil
	}
	var out []outcome
	single, double := false, false
	for _, line := range strings.Split(string(src), "\n") {
		escaped := false
		for i := 0; i < len(line); i++ {
			ch := line[i]
			switch {
			case escaped:
				escaped = false
			case ch == '\\' && !single:
				escaped = true
			case ch == '\'' && !double:
				single = !single
			case ch == '"' && !single:
				double = !double
			case ch == '#' && !single && !double && (i == 0 || strings.IndexByte(" \t;&|()", line[i-1]) >= 0):
				out = append(out, outcome{"comment", ast.String(line[i:])})
				i = len(line)
			}
		}
	}
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
	mode := os.FileMode(0o644)
	if info, err := os.Stat(path); err == nil {
		mode = info.Mode().Perm()
	}
	return os.WriteFile(path, data, mode)
}

func tryChange(k *knowledge, tool, change string) []outcome {
	if os.Getenv(changeVariable) != "" {
		return nil
	}
	dir, err := os.MkdirTemp("", "change-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	if copyFolder(".", dir) != nil {
		return nil
	}
	if k.executes(toolsFile, "adds line", 3) {
		var adds [][2]string
		for _, row := range k.facts("adds line", 3) {
			if constText(row[0]) == change {
				adds = append(adds, [2]string{constText(row[1]), constText(row[2])})
			}
		}
		sort.Slice(adds, func(i, j int) bool {
			if adds[i][0] != adds[j][0] {
				return adds[i][0] < adds[j][0]
			}
			return adds[i][1] < adds[j][1]
		})
		for _, a := range adds {
			if !filepath.IsLocal(a[0]) || appendLine(filepath.Join(dir, a[0]), a[1]) != nil {
				return nil
			}
		}
	}
	var places []ast.Constant
	if k.executes(toolsFile, "reads", 2) {
		places = k.objects("reads", tool)
	}
	var out []outcome
	for _, f := range k.objects("runs", tool) {
		file := constText(f)
		if !filepath.IsLocal(file) {
			continue
		}
		ctx, cancel := context.WithTimeout(context.Background(), runLimit)
		cmd := exec.CommandContext(ctx, "sh", file)
		cmd.Dir = dir
		cmd.Env = append(os.Environ(), changeVariable+"="+change)
		var stdout, stderr bytes.Buffer
		cmd.Stdout, cmd.Stderr = &stdout, &stderr
		cmd.Run()
		cancel()
		code := -1
		if cmd.ProcessState != nil {
			code = cmd.ProcessState.ExitCode()
		}
		out = append(out, outcome{"exit code", ast.Number(int64(code))})
		for _, p := range places {
			switch constText(p) {
			case "standard output":
				out = append(out, reasons(stdout.String())...)
			case "standard error":
				out = append(out, reasons(stderr.String())...)
			}
		}
	}
	return out
}

func reasons(text string) []outcome {
	clauses, _ := readText("the output", text)
	var out []outcome
	seen := map[string]bool{}
	add := func(field string, value ast.Constant) {
		key := field + "\x00" + value.String()
		if !seen[key] {
			seen[key] = true
			out = append(out, outcome{field, value})
		}
	}
	for _, c := range clauses {
		h := c.head
		if len(c.body) > 0 || h.kind != atomLit {
			continue
		}
		var args []ast.Constant
		for _, t := range h.args {
			if v, ok := t.constant(); ok {
				args = append(args, v)
			}
		}
		if len(args) != len(h.args) {
			continue
		}
		switch {
		case h.word == "breaks" && len(args) == 2:
			add("broke", args[1])
			add("why", ast.String(h.sentence()))
		case h.word == "a problem" && len(args) == 1:
			add("why", ast.String(h.sentence()))
		}
	}
	return out
}
