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

var toolsExecutes = []string{"runs/2", "reads/2", "adds_line/3", "holds_because/2"}

var toolsCreates = []string{"returned/3"}

type result struct {
	field string
	value value
}

func runTool(tool string, input value, m *model, order map[string]int) []result {
	switch tool {
	case "list":
		return listTool(input)
	case "find go comments":
		return commentTool(input, goComments)
	case "find sh comments":
		return commentTool(input, shComments)
	case "try":
		return tryTool(input, m, order)
	}
	return nil
}

func listTool(input value) []result {
	if input.key() != text("the folder").key() {
		return nil
	}
	var out []result
	for _, file := range folderFiles(".") {
		out = append(out, result{"file", text(file)})
	}
	return out
}

func folderFiles(root string) []string {
	var files []string
	filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		if d.IsDir() {
			if path != root && d.Name() == ".git" {
				return filepath.SkipDir
			}
			return nil
		}
		if d.Type().IsRegular() {
			if rel, err := filepath.Rel(root, path); err == nil {
				files = append(files, filepath.ToSlash(rel))
			}
		}
		return nil
	})
	sort.Strings(files)
	return files
}

func commentTool(input value, find func([]byte) []string) []result {
	if input.kind != textValue || !filepath.IsLocal(input.text) {
		return nil
	}
	src, err := os.ReadFile(filepath.FromSlash(input.text))
	if err != nil {
		return nil
	}
	var out []result
	for _, c := range find(src) {
		out = append(out, result{"comment", text(c)})
	}
	return out
}

func goComments(src []byte) []string {
	files := token.NewFileSet()
	var s scanner.Scanner
	s.Init(files.AddFile("", files.Base(), len(src)), src, nil, scanner.ScanComments)
	var out []string
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, strings.NewReplacer("\r\n", " ", "\n", " ", "\r", "").Replace(lit))
		}
	}
}

func shComments(src []byte) []string {
	var out []string
	single, double := false, false
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case single:
			single = c != '\''
		case double:
			if c == '\\' {
				i++
			}
			double = c != '"'
		case c == '\\':
			i++
		case c == '\'':
			single = true
		case c == '"':
			double = true
		case c == '#' && (i == 0 || strings.IndexByte(" \t\n;&|()<>", src[i-1]) >= 0):
			end := bytes.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			out = append(out, strings.TrimRight(string(src[i:i+end]), "\r"))
			i += end - 1
		}
	}
	return out
}

func tryTool(change value, m *model, order map[string]int) []result {
	if os.Getenv(changeVariable) != "" || change.kind != textValue {
		return nil
	}
	script, ok := single(m.objects("runs", text("try")))
	place, ok2 := single(m.objects("reads", text("try")))
	if !ok || !ok2 || script.kind != textValue || !filepath.IsLocal(script.text) {
		return nil
	}
	var lines []fact
	for _, f := range m.get("adds_line", 3) {
		if f.args[0].key() == change.key() {
			lines = append(lines, f)
		}
	}
	position := func(f fact) int {
		if p, ok := order[f.key()]; ok {
			return p
		}
		return len(order)
	}
	sort.SliceStable(lines, func(i, j int) bool {
		if position(lines[i]) != position(lines[j]) {
			return position(lines[i]) < position(lines[j])
		}
		return lines[i].key() < lines[j].key()
	})
	here, err := os.Getwd()
	if err != nil {
		return nil
	}
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	folder := filepath.Join(dir, filepath.Base(here))
	if err := copyFolder(here, folder); err != nil {
		return nil
	}
	for _, l := range lines {
		if err := appendLine(folder, l.args[1], l.args[2]); err != nil {
			return nil
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", filepath.FromSlash(script.text))
	cmd.Dir = folder
	cmd.Env = append(os.Environ(), changeVariable+"="+change.text)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			return nil
		}
		code = exit.ExitCode()
	}
	var view string
	switch place.words() {
	case "standard output":
		view = stdout.String()
	case "standard error":
		view = stderr.String()
	default:
		return nil
	}
	out := []result{{"exit code", number(int64(code))}}
	seen := map[string]bool{}
	stmts, _ := parseText(place.words(), view)
	for _, s := range stmts {
		if len(s.conds) > 0 || len(s.head.args) != 2 || !s.head.ground() {
			continue
		}
		var res result
		switch s.head.pred {
		case "breaks":
			res = result{"broke", s.head.args[1]}
		case "holds_because":
			res = result{"explanation", text(s.head.plain())}
		default:
			continue
		}
		if !seen[res.field+res.value.key()] {
			seen[res.field+res.value.key()] = true
			out = append(out, res)
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
			if path != from && d.Name() == ".git" {
				return filepath.SkipDir
			}
			return os.MkdirAll(target, 0o755)
		}
		if !d.Type().IsRegular() {
			return nil
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		src, err := os.Open(path)
		if err != nil {
			return err
		}
		defer src.Close()
		dst, err := os.OpenFile(target, os.O_CREATE|os.O_TRUNC|os.O_WRONLY, info.Mode().Perm())
		if err != nil {
			return err
		}
		if _, err := io.Copy(dst, src); err != nil {
			dst.Close()
			return err
		}
		return dst.Close()
	})
}

func appendLine(folder string, file, line value) error {
	if file.kind != textValue || !filepath.IsLocal(file.text) {
		return errors.New("a change can only add lines to files in the folder")
	}
	path := filepath.Join(folder, filepath.FromSlash(file.text))
	old, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	content := line.words() + "\n"
	if len(old) > 0 && old[len(old)-1] != '\n' {
		content = "\n" + content
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	f, err := os.OpenFile(path, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	if _, err := f.WriteString(content); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}
