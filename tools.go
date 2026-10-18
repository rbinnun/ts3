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
	"time"

	"mvdan.cc/sh/v3/syntax"
)

type found struct {
	field string
	value value
}

type tool func(input value, k *knowledge) ([]found, error)

var toolbox = map[string]tool{
	"list":             list,
	"find go comments": findGoComments,
	"find sh comments": findShComments,
	"try":              try,
}

func list(input value, k *knowledge) ([]found, error) {
	if input != text("the folder") {
		return nil, fmt.Errorf("list can only list the folder")
	}
	entries, err := os.ReadDir(".")
	if err != nil {
		return nil, err
	}
	var out []found
	for _, e := range entries {
		out = append(out, found{"file", text(e.Name())})
	}
	return out, nil
}

func findGoComments(input value, k *knowledge) ([]found, error) {
	src, err := os.ReadFile(input.String())
	if err != nil {
		return nil, err
	}
	var s scanner.Scanner
	s.Init(token.NewFileSet().AddFile(input.String(), -1, len(src)), src, nil, scanner.ScanComments)
	var out []found
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out, nil
		}
		if tok == token.COMMENT {
			out = append(out, found{"comment", text(oneLine(lit))})
		}
	}
}

func findShComments(input value, k *knowledge) ([]found, error) {
	src, err := os.ReadFile(input.String())
	if err != nil {
		return nil, err
	}
	file, err := syntax.NewParser(syntax.KeepComments(true)).Parse(bytes.NewReader(src), input.String())
	if err != nil {
		return nil, err
	}
	var out []found
	syntax.Walk(file, func(n syntax.Node) bool {
		if c, ok := n.(*syntax.Comment); ok {
			out = append(out, found{"comment", text(oneLine("#" + c.Text))})
		}
		return true
	})
	return out, nil
}

func try(input value, k *knowledge) ([]found, error) {
	if k.change {
		return nil, errors.New("a change cannot try another change")
	}
	script, err := k.only("runs", "try")
	if err != nil {
		return nil, err
	}
	place, err := k.only("reads", "try")
	if err != nil {
		return nil, err
	}
	if place != "standard output" {
		return nil, fmt.Errorf("try cannot read %s", place)
	}
	room, err := os.MkdirTemp("", "change-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(room)
	if err := copyFolder(".", room); err != nil {
		return nil, err
	}
	for _, f := range k.facts("adds line") {
		if len(f.args) == 3 && f.args[0] == input {
			if err := addLine(room, f.args[1].String(), f.args[2].String()); err != nil {
				return nil, err
			}
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Minute)
	defer cancel()
	run := exec.CommandContext(ctx, "sh", script)
	run.Dir = room
	run.Env = append(os.Environ(), changeSignal+"=yes")
	var out bytes.Buffer
	run.Stdout = &out
	code := 0
	if err := run.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) || ctx.Err() != nil {
			return nil, err
		}
		code = exit.ExitCode()
	}
	results := []found{{"exit code", count(int64(code))}}
	rules, _ := readText("standard output", out.String())
	for _, r := range rules {
		if len(r.conds) > 0 || len(r.blanks()) > 0 || len(r.head.args) != 2 {
			continue
		}
		switch r.head.pred {
		case "breaks":
			results = append(results, found{"broke", r.head.args[1].val})
		case "holds because":
			results = append(results, found{"why", r.head.args[1].val})
		}
	}
	return results, nil
}

func copyFolder(from, to string) error {
	return filepath.WalkDir(from, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(from, path)
		if err != nil || rel == "." {
			return err
		}
		target := filepath.Join(to, rel)
		info, err := d.Info()
		if err != nil {
			return err
		}
		switch {
		case d.IsDir():
			return os.MkdirAll(target, 0o755)
		case info.Mode()&fs.ModeSymlink != 0:
			link, err := os.Readlink(path)
			if err != nil {
				return err
			}
			return os.Symlink(link, target)
		case info.Mode().IsRegular():
			data, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			return os.WriteFile(target, data, info.Mode().Perm())
		}
		return nil
	})
}

func addLine(room, name, line string) error {
	if !filepath.IsLocal(name) {
		return fmt.Errorf("%s is not a file in the folder", name)
	}
	path := filepath.Join(room, name)
	old, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(old) > 0 && old[len(old)-1] != '\n' {
		old = append(old, '\n')
	}
	return os.WriteFile(path, append(old, []byte(line+"\n")...), 0o644)
}
