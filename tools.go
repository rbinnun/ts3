package main

import (
	"bytes"
	"go/scanner"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
)

const (
	theFolder     = "the folder"
	aChange       = "a change"
	shellWordEnds = " \t\n;&|()"
)

type finding struct {
	field string
	value ast.Constant
}

type tool struct {
	live bool
	run  func(r *run, name, input string) []finding
}

var toolbox = map[string]tool{
	"list":                {run: list},
	"count lines":         {run: countLines},
	"find go comments":    {run: findGoComments},
	"find sh comments":    {run: findShComments},
	"parse":               {run: parseRules},
	"read a rule":         {run: readRule},
	"see what fired":      {live: true, run: seeWhatFired},
	"try":                 {run: try},
	"read a fact pattern": {run: readPattern},
}

func says(field string, value ast.Constant) finding {
	return finding{field, value}
}

func folderOf(input string) string {
	if input == theFolder {
		return "."
	}
	return input
}

func filesIn(dir string) []string {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var files []string
	for _, e := range entries {
		if e.Type().IsRegular() {
			files = append(files, e.Name())
		}
	}
	return files
}

func list(r *run, name, input string) []finding {
	var found []finding
	for _, f := range filesIn(folderOf(input)) {
		found = append(found, says("file", ast.String(f)))
	}
	return found
}

func countLines(r *run, name, file string) []finding {
	data, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	n := bytes.Count(data, []byte("\n"))
	if len(data) > 0 && data[len(data)-1] != '\n' {
		n++
	}
	return []finding{says("lines", ast.Number(int64(n)))}
}

func findGoComments(r *run, name, file string) []finding {
	src, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	fset := token.NewFileSet()
	var s scanner.Scanner
	s.Init(fset.AddFile(file, fset.Base(), len(src)), src, nil, scanner.ScanComments)
	var found []finding
	for {
		_, tok, lit := s.Scan()
		switch tok {
		case token.EOF:
			return found
		case token.COMMENT:
			found = append(found, says("comment", ast.String(lit)))
		}
	}
}

func findShComments(r *run, name, file string) []finding {
	src, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	var found []finding
	quote := byte(0)
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case quote == '\'':
			if c == '\'' {
				quote = 0
			}
		case c == '\\':
			i++
		case quote == '"':
			if c == '"' {
				quote = 0
			}
		case c == '\'' || c == '"':
			quote = c
		case c == '#' && (i == 0 || strings.IndexByte(shellWordEnds, src[i-1]) >= 0):
			end := bytes.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			found = append(found, says("comment", ast.String(string(src[i:i+end]))))
			i += end
		}
	}
	return found
}

func rulesOf(file string) []*rule {
	data, err := os.ReadFile(file)
	if err != nil {
		return nil
	}
	var rules []*rule
	for _, rl := range readPlain(file, string(data)).rules {
		if !rl.declared {
			rules = append(rules, rl)
		}
	}
	return rules
}

func parseRules(r *run, name, file string) []finding {
	var found []finding
	for _, rl := range rulesOf(file) {
		found = append(found, says("rule", ast.String(rl.id)))
	}
	return found
}

func readRule(r *run, name, id string) []finding {
	cut := strings.LastIndex(id, ":")
	if cut < 0 {
		return nil
	}
	for _, rl := range rulesOf(id[:cut]) {
		if rl.id != id {
			continue
		}
		found := []finding{says("word it defines", ast.String(wordOf(rl.head.name)))}
		if law, ok := rl.law(); ok {
			found = append(found, says("law it lays down", ast.String(law)))
		}
		seen := map[string]bool{}
		for _, p := range rl.body {
			if p.shape == relationShape && !seen[p.name] {
				seen[p.name] = true
				found = append(found, says("word it refers to", ast.String(wordOf(p.name))))
			}
		}
		return found
	}
	return nil
}

func (rl *rule) law() (string, bool) {
	h := rl.head
	if h.name != nameOf("breaks") || len(h.args) != 2 || !h.args[1].isText() {
		return "", false
	}
	return h.args[1].text, true
}

func seeWhatFired(r *run, name, input string) []finding {
	var ids []string
	for id := range r.fired {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	var found []finding
	for _, id := range ids {
		found = append(found, says("rule that fired", ast.String(id)))
	}
	return found
}

func readPattern(r *run, name, pattern string) []finding {
	line, ok := patternLine(pattern)
	if !ok {
		return nil
	}
	p, err := readPremise(line)
	if err != nil || p.shape != relationShape {
		return nil
	}
	return []finding{says("word it names", ast.String(wordOf(p.name)))}
}

func try(r *run, name, change string) []finding {
	script, ok := r.lookup("runs", name)
	if !ok {
		return nil
	}
	stream, _ := r.lookup("reads", name)
	dir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil
	}
	defer os.RemoveAll(dir)
	for _, f := range filesIn(".") {
		if copyFile(f, filepath.Join(dir, f)) != nil {
			return nil
		}
	}
	for _, a := range r.facts("adds line", ast.String(change), ast.Variable{Symbol: "File"}, ast.Variable{Symbol: "Line"}) {
		if addLine(filepath.Join(dir, textOf(a.Args[1])), textOf(a.Args[2])) != nil {
			return nil
		}
	}
	cmd := exec.Command("sh", script)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), kindOfRun+"="+aChange)
	var out bytes.Buffer
	if stream == standardError {
		cmd.Stderr = &out
	} else {
		cmd.Stdout = &out
	}
	cmd.Run()
	if cmd.ProcessState == nil {
		return nil
	}
	found := []finding{says("exit code", ast.Number(int64(cmd.ProcessState.ExitCode())))}
	for _, line := range strings.Split(out.String(), "\n") {
		p, err := readPremise(line)
		if err != nil || p.shape != relationShape {
			continue
		}
		switch {
		case p.name == nameOf("breaks") && len(p.args) == 2 && p.args[1].isText():
			found = append(found, says("broke", ast.String(p.args[1].text)))
		case p.name == nameOf("never fired") && len(p.args) == 1 && p.args[0].isText():
			found = append(found, says("never fired", ast.String(p.args[0].text)))
		}
	}
	return found
}

func copyFile(from, to string) error {
	info, err := os.Stat(from)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(from)
	if err != nil {
		return err
	}
	return os.WriteFile(to, data, info.Mode().Perm())
}

func addLine(file, line string) error {
	data, err := os.ReadFile(file)
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line+"\n"...)
	return os.WriteFile(file, data, 0o644)
}
