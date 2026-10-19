package main

import (
	"bytes"
	"context"
	"errors"
	"go/scanner"
	"go/token"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"time"
)

const (
	toolsFile  = "tools.go"
	thisFolder = "the folder"
)

type result struct {
	field string
	value val
}

type tool func(m *machine, name, input string) []result

var catalog = map[string]tool{
	"list":             list,
	"find go comments": findGoComments,
	"find sh comments": findShComments,
	"try":              try,
}

func (m *machine) call(command, name, input string) [][]val {
	run, ok := catalog[name]
	if !ok {
		return nil
	}
	var out [][]val
	for _, r := range run(m, name, input) {
		out = append(out, []val{text(command), text(r.field), r.value})
	}
	return out
}

func folderOf(input string) (string, bool) {
	if input == thisFolder {
		return ".", true
	}
	return input, filepath.IsLocal(input)
}

func filesIn(dir string) []string {
	var out []string
	filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() {
			return nil
		}
		if rel, err := filepath.Rel(dir, path); err == nil {
			out = append(out, filepath.ToSlash(rel))
		}
		return nil
	})
	sort.Strings(out)
	return out
}

func list(m *machine, name, input string) []result {
	dir, ok := folderOf(input)
	if !ok {
		return nil
	}
	var out []result
	for _, f := range filesIn(dir) {
		out = append(out, result{"file", text(f)})
	}
	return out
}

func readLocal(input string) ([]byte, bool) {
	if !filepath.IsLocal(input) {
		return nil, false
	}
	src, err := os.ReadFile(input)
	return src, err == nil
}

func findGoComments(m *machine, name, input string) []result {
	src, ok := readLocal(input)
	if !ok {
		return nil
	}
	files := token.NewFileSet()
	file := files.AddFile(input, files.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, func(token.Position, string) {}, scanner.ScanComments)
	var out []result
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, result{"comment", text(oneLine(lit))})
		}
	}
}

func findShComments(m *machine, name, input string) []result {
	src, ok := readLocal(input)
	if !ok {
		return nil
	}
	var out []result
	s := string(src)
	wordStart := true
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '\\':
			i++
			wordStart = false
		case c == '\'':
			if j := strings.IndexByte(s[i+1:], '\''); j >= 0 {
				i += j + 1
			} else {
				i = len(s)
			}
			wordStart = false
		case c == '"':
			for i++; i < len(s) && s[i] != '"'; i++ {
				if s[i] == '\\' {
					i++
				}
			}
			wordStart = false
		case c == '#' && wordStart:
			end := strings.IndexByte(s[i:], '\n')
			if end < 0 {
				end = len(s) - i
			}
			out = append(out, result{"comment", text(oneLine(s[i : i+end]))})
			i += end - 1
		case strings.IndexByte(" \t\n;&|()<>", c) >= 0:
			wordStart = true
		default:
			wordStart = false
		}
	}
	return out
}

func try(m *machine, name, change string) []result {
	scripts := m.objectsOf("[tool] runs [file]", name)
	if len(scripts) != 1 {
		return nil
	}
	places := m.objectsOf("[tool] reads [place]", name)
	here, err := os.Getwd()
	if err != nil {
		return nil
	}
	top, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(top)
	there := filepath.Join(top, filepath.Base(here))
	for _, f := range filesIn(".") {
		if !copyFile(f, filepath.Join(there, filepath.FromSlash(f))) {
			return nil
		}
	}
	for _, a := range m.ordered(m.predOf("[change] adds line [file] [line]")) {
		if len(a) != 3 || a[0].String() != change || !filepath.IsLocal(a[1].String()) {
			continue
		}
		if !addLine(filepath.Join(there, filepath.FromSlash(a[1].String())), a[2].String()) {
			return nil
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", scripts[0].String(), change)
	cmd.Dir = there
	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = io.Discard
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return nil
		}
		code = exit.ExitCode()
	}
	out := []result{{"exit code", number(int64(code))}}
	for _, p := range places {
		if p.String() != "standard output" {
			continue
		}
		for _, ln := range strings.Split(stdout.String(), "\n") {
			st, ok := readStmt(ln)
			if !ok || st.prop != "" {
				continue
			}
			switch {
			case st.verb == "breaks" && len(st.objs) == 1 && st.objs[0].blank == "":
				out = append(out, result{"broke", st.objs[0].v})
			case st.verb == "holds because":
				out = append(out, result{"explanation", text(ln)})
			}
		}
	}
	return out
}

func copyFile(from, to string) bool {
	info, err := os.Stat(from)
	if err != nil {
		return false
	}
	data, err := os.ReadFile(from)
	if err != nil {
		return false
	}
	if os.MkdirAll(filepath.Dir(to), 0o755) != nil {
		return false
	}
	return os.WriteFile(to, data, info.Mode().Perm()) == nil
}

func addLine(path, line string) bool {
	data, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return false
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line+"\n"...)
	if os.MkdirAll(filepath.Dir(path), 0o755) != nil {
		return false
	}
	return os.WriteFile(path, data, 0o644) == nil
}
