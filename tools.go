package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/scanner"
	"go/token"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

const (
	toolsFile   = "tools.go"
	theFolder   = "the folder"
	tryTimeout  = 20 * time.Minute
	shellBreaks = " \t\n;&|()<>`"
)

type Call struct {
	Command Value
	Tool    Value
	Input   Value
}

type Returned struct {
	Field string
	Value Value
}

type tool func(e *Engine, m *Model, input Value) []Returned

var tools map[string]tool

func init() {
	tools = map[string]tool{
		"list":             listTool,
		"find go comments": goCommentsTool,
		"find sh comments": shCommentsTool,
		"try":              tryTool,
	}
}

func (e *Engine) callTools(calls []Call, m *Model) {
	results := make([][]Returned, len(calls))
	limit := runtime.NumCPU()
	if limit < 2 {
		limit = 2
	}
	gate := make(chan struct{}, limit)
	var wg sync.WaitGroup
	for i, c := range calls {
		if c.Tool.Num {
			continue
		}
		t, ok := tools[c.Tool.S]
		if !ok {
			continue
		}
		wg.Add(1)
		go func(i int, input Value, t tool) {
			defer wg.Done()
			gate <- struct{}{}
			defer func() { <-gate }()
			results[i] = t(e, m, input)
		}(i, c.Input, t)
	}
	wg.Wait()
	for i, c := range calls {
		for _, r := range results[i] {
			e.create(toolsFile, "returned", c.Command, text(r.Field), r.Value)
		}
	}
}

func listTool(e *Engine, m *Model, input Value) []Returned {
	dir := input.plain()
	if input == text(theFolder) {
		dir = "."
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var out []Returned
	for _, entry := range entries {
		out = append(out, Returned{"file", text(entry.Name())})
	}
	return out
}

func goCommentsTool(e *Engine, m *Model, input Value) []Returned {
	src, err := os.ReadFile(input.plain())
	if err != nil {
		return nil
	}
	fset := token.NewFileSet()
	file := fset.AddFile(input.plain(), fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, scanner.ScanComments)
	var out []Returned
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, Returned{"comment", text(lit)})
		}
	}
}

func shCommentsTool(e *Engine, m *Model, input Value) []Returned {
	src, err := os.ReadFile(input.plain())
	if err != nil {
		return nil
	}
	var out []Returned
	s := string(src)
	inSingle, inDouble, wordStart := false, false, true
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case inSingle:
			inSingle = c != '\''
		case inDouble:
			if c == '\\' {
				i++
			} else if c == '"' {
				inDouble = false
			}
		case c == '\\':
			i++
			wordStart = false
		case c == '\'':
			inSingle, wordStart = true, false
		case c == '"':
			inDouble, wordStart = true, false
		case c == '#' && wordStart:
			end := strings.IndexByte(s[i:], '\n')
			if end < 0 {
				end = len(s) - i
			}
			out = append(out, Returned{"comment", text(strings.TrimRight(s[i:i+end], "\r"))})
			i += end - 1
		default:
			wordStart = strings.IndexByte(shellBreaks, c) >= 0
		}
	}
	return out
}

func (e *Engine) before(a, b Fact) bool {
	pa, oka := e.positions[a.key()]
	pb, okb := e.positions[b.key()]
	switch {
	case oka && okb:
		return pa < pb
	case oka != okb:
		return oka
	}
	return lessValues(a.Args, b.Args)
}

func tryTool(e *Engine, m *Model, change Value) []Returned {
	if os.Getenv(changeVariable) != "" {
		e.problem("the change %s cannot try the change %s", os.Getenv(changeVariable), change.plain())
		return nil
	}
	var adds []Fact
	for _, f := range m.facts["adds line"] {
		if len(f.Args) == 3 && f.Args[0] == change {
			adds = append(adds, f)
		}
	}
	sort.SliceStable(adds, func(i, j int) bool { return e.before(adds[i], adds[j]) })
	runs := e.objects(m, "runs", "try")
	reads := e.objects(m, "reads", "try")
	dir, err := os.MkdirTemp("", "change-")
	if err != nil {
		e.problem("try cannot make room for %s: %v", change.plain(), err)
		return nil
	}
	defer os.RemoveAll(dir)
	folder := filepath.Join(dir, "folder")
	if err := copyFolder(".", folder); err != nil {
		e.problem("try cannot copy the folder for %s: %v", change.plain(), err)
		return nil
	}
	for _, f := range adds {
		if err := addLine(dir, folder, f.Args[1].plain(), f.Args[2].plain()); err != nil {
			e.problem("the change %s cannot add a line to %s: %v", change.plain(), f.Args[1].plain(), err)
			return nil
		}
	}
	var out []Returned
	for _, run := range runs {
		ctx, cancel := context.WithTimeout(context.Background(), tryTimeout)
		cmd := exec.CommandContext(ctx, "sh", run)
		cmd.Dir = folder
		cmd.Env = append(os.Environ(), changeVariable+"="+change.plain())
		var stdout, stderr bytes.Buffer
		cmd.Stdout, cmd.Stderr = &stdout, &stderr
		err := cmd.Run()
		cancel()
		var exit *exec.ExitError
		if err != nil && !errors.As(err, &exit) {
			e.problem("try cannot run %s for %s: %v", run, change.plain(), err)
			continue
		}
		out = append(out, Returned{"exit code", number(int64(cmd.ProcessState.ExitCode()))})
		for _, place := range reads {
			switch place {
			case "standard output":
				out = append(out, readView(stdout.String())...)
			case "standard error":
				out = append(out, readView(stderr.String())...)
			default:
				e.problem("try cannot read %s", place)
			}
		}
	}
	return out
}

func readView(output string) []Returned {
	rules, _ := parsePlainText("the output", output)
	var out []Returned
	for _, r := range rules {
		if r.Bad || len(r.Conds) > 0 || hasBlanks(r.Head) || r.Head.IsForm || len(r.Head.Args) != 2 {
			continue
		}
		switch r.Head.Pred {
		case "breaks":
			out = append(out, Returned{"broke", r.Head.Args[1].Val})
		case "holds because":
			out = append(out, Returned{"explanation", text(renderAtom(r.Head, false))})
		}
	}
	return out
}

func copyFolder(from, to string) error {
	return filepath.WalkDir(from, func(path string, d fs.DirEntry, err error) error {
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
		src, err := os.Open(path)
		if err != nil {
			return err
		}
		defer src.Close()
		info, err := src.Stat()
		if err != nil {
			return err
		}
		dst, err := os.OpenFile(target, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, info.Mode().Perm())
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

func addLine(room, folder, file, line string) error {
	target := filepath.Join(folder, file)
	if rel, err := filepath.Rel(room, target); err != nil || rel == ".." || strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
		return fmt.Errorf("%s is outside the copy of the folder", file)
	}
	existing, err := os.ReadFile(target)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	f, err := os.OpenFile(target, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	if len(existing) > 0 && existing[len(existing)-1] != '\n' {
		line = "\n" + line
	}
	if _, err := f.WriteString(line + "\n"); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}
