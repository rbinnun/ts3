package main

import (
	"bytes"
	"errors"
	"fmt"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/parse"
)

type finding struct {
	field string
	value ast.Constant
}

type tool struct {
	remembers bool
	use       func(m *machine, input ast.Constant) ([]finding, error)
}

var tools map[string]tool

func init() {
	tools = map[string]tool{
		"list":           {remembers: true, use: list},
		"count lines":    {remembers: true, use: countLines},
		"find comments":  {remembers: true, use: findComments},
		"parse":          {remembers: true, use: parseFile},
		"read a rule":    {remembers: true, use: readRule},
		"see what fired": {remembers: false, use: seeWhatFired},
		"try":            {remembers: true, use: try},
	}
}

func says(field string, values ...string) []finding {
	var out []finding
	for _, v := range values {
		out = append(out, finding{field, ast.String(v)})
	}
	return out
}

func list(m *machine, input ast.Constant) ([]finding, error) {
	rel, err := input.StringValue()
	if err != nil {
		return nil, errors.New("list needs a folder name")
	}
	root, err := m.path(rel)
	if err != nil {
		return nil, err
	}
	files, err := filesUnder(root)
	if err != nil {
		return nil, err
	}
	return says("file", files...), nil
}

func filesUnder(root string) ([]string, error) {
	var files []string
	err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		rel, err := filepath.Rel(root, p)
		if err != nil {
			return err
		}
		files = append(files, filepath.ToSlash(rel))
		return nil
	})
	sort.Strings(files)
	return files, err
}

func readInput(m *machine, input ast.Constant) (string, []byte, error) {
	rel, err := input.StringValue()
	if err != nil {
		return "", nil, fmt.Errorf("%s does not name a file", input)
	}
	full, err := m.path(rel)
	if err != nil {
		return "", nil, err
	}
	data, err := os.ReadFile(full)
	return rel, data, err
}

func countLines(m *machine, input ast.Constant) ([]finding, error) {
	_, data, err := readInput(m, input)
	if err != nil {
		return nil, err
	}
	n := bytes.Count(data, []byte("\n"))
	if len(data) > 0 && data[len(data)-1] != '\n' {
		n++
	}
	return []finding{{"lines", ast.Number(int64(n))}}, nil
}

func findComments(m *machine, input ast.Constant) ([]finding, error) {
	pathTerm, languageTerm, err := input.PairValue()
	if err != nil {
		return nil, errors.New("find comments needs a pair of a file and its language")
	}
	language, err := languageTerm.StringValue()
	if err != nil {
		return nil, errors.New("find comments needs a language name")
	}
	rel, data, err := readInput(m, pathTerm)
	if err != nil {
		return nil, err
	}
	var comments []string
	switch language {
	case "go":
		comments, err = goComments(rel, data)
	case "mangle":
		comments = hashComments(string(data), false)
	case "sh":
		comments = hashComments(string(data), true)
	default:
		return nil, fmt.Errorf("cannot find comments in %s", language)
	}
	if err != nil {
		return nil, err
	}
	return says("comment", comments...), nil
}

func goComments(name string, src []byte) ([]string, error) {
	fset := token.NewFileSet()
	file := fset.AddFile(name, fset.Base(), len(src))
	var problems scanner.ErrorList
	var s scanner.Scanner
	s.Init(file, src, func(pos token.Position, msg string) { problems.Add(pos, msg) }, scanner.ScanComments)
	var comments []string
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			break
		}
		if tok == token.COMMENT {
			comments = append(comments, lit)
		}
	}
	return comments, problems.Err()
}

func hashComments(src string, shell bool) []string {
	var comments []string
	i := 0
	if shell && strings.HasPrefix(src, "#!") {
		i = lineEnd(src, 0)
	}
	quote := byte(0)
	for ; i < len(src); i++ {
		c := src[i]
		if quote != 0 {
			switch {
			case c == '\\' && quote != '`' && !(shell && quote == '\''):
				i++
			case c == quote:
				quote = 0
			case c == '\n' && !shell && quote != '`':
				quote = 0
			}
			continue
		}
		switch {
		case c == '"' || c == '\'' || (c == '`' && !shell):
			quote = c
		case c == '\\' && shell:
			i++
		case c == '#' && (!shell || wordStart(src, i)):
			end := lineEnd(src, i)
			comments = append(comments, strings.TrimRight(src[i:end], "\r"))
			i = end
		}
	}
	return comments
}

func lineEnd(src string, i int) int {
	if n := strings.IndexByte(src[i:], '\n'); n >= 0 {
		return i + n
	}
	return len(src)
}

func wordStart(src string, i int) bool {
	return i == 0 || strings.IndexByte(" \t\n;&|()<>", src[i-1]) >= 0
}

func parseFile(m *machine, input ast.Constant) ([]finding, error) {
	rel, data, err := readInput(m, input)
	if err != nil {
		return nil, err
	}
	unit, err := parse.Unit(bytes.NewReader(data))
	if err != nil {
		return nil, fmt.Errorf("%s does not parse: %s", rel, strings.TrimSpace(err.Error()))
	}
	var rules []string
	for _, c := range unit.Clauses {
		rules = append(rules, c.String())
	}
	return says("rule", rules...), nil
}

func readRule(m *machine, input ast.Constant) ([]finding, error) {
	text, err := input.StringValue()
	if err != nil {
		return nil, fmt.Errorf("%s is not a rule", input)
	}
	unit, err := parse.Unit(strings.NewReader(text))
	if err != nil {
		return nil, fmt.Errorf("the rule does not parse: %s", strings.TrimSpace(err.Error()))
	}
	if len(unit.Clauses) != 1 {
		return nil, fmt.Errorf("%q holds %d rules, not one", text, len(unit.Clauses))
	}
	rule := unit.Clauses[0]
	out := says("head", rule.Head.Predicate.Symbol)
	if len(rule.Head.Args) > 0 {
		if c, ok := rule.Head.Args[0].(ast.Constant); ok {
			out = append(out, finding{"first argument", c})
		}
	}
	seen := map[string]bool{}
	for _, p := range rule.Premises {
		var sym ast.PredicateSym
		switch t := p.(type) {
		case ast.Atom:
			sym = t.Predicate
		case ast.NegAtom:
			sym = t.Atom.Predicate
		default:
			continue
		}
		if sym.IsBuiltin() || seen[sym.Symbol] {
			continue
		}
		seen[sym.Symbol] = true
		out = append(out, says("uses", sym.Symbol)...)
	}
	return out, nil
}

func seeWhatFired(m *machine, input ast.Constant) ([]finding, error) {
	rel, err := input.StringValue()
	if err != nil {
		return nil, fmt.Errorf("%s does not name a file", input)
	}
	return says("fired", m.firedIn(rel)...), nil
}

func try(m *machine, input ast.Constant) ([]finding, error) {
	if m.effect == "try" {
		return nil, errors.New("a run that is itself a change does not try further changes")
	}
	pathTerm, lineTerm, err := input.PairValue()
	if err != nil {
		return nil, errors.New("try needs a pair of a file and a line")
	}
	rel, err := pathTerm.StringValue()
	if err != nil {
		return nil, fmt.Errorf("%s does not name a file", pathTerm)
	}
	line, err := lineTerm.StringValue()
	if err != nil {
		return nil, fmt.Errorf("%s is not a line", lineTerm)
	}
	if !filepath.IsLocal(rel) {
		return nil, fmt.Errorf("%s is outside the folder", rel)
	}
	copyDir, err := os.MkdirTemp("", "try-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(copyDir)
	if err := copyFolder(m.dir, copyDir); err != nil {
		return nil, err
	}
	if err := addLine(filepath.Join(copyDir, filepath.FromSlash(rel)), line); err != nil {
		return nil, err
	}
	o := run(copyDir, m.spec, "try")
	var out []finding
	if o.answer != "" {
		out = append(out, says("conforms", o.answer)...)
	}
	broke := map[string]bool{}
	o.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "violation", Arity: 2}), func(a ast.Atom) error {
		if c, ok := a.Args[0].(ast.Constant); ok && !broke[c.String()] {
			broke[c.String()] = true
			out = append(out, finding{"broke", c})
		}
		return nil
	})
	o.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: "unfired", Arity: 2}), func(a ast.Atom) error {
		where, ok1 := a.Args[0].(ast.Constant)
		rule, ok2 := a.Args[1].(ast.Constant)
		if ok1 && ok2 {
			out = append(out, finding{"unfired", ast.Pair(&where, &rule)})
		}
		return nil
	})
	return out, nil
}

func copyFolder(from, to string) error {
	files, err := filesUnder(from)
	if err != nil {
		return err
	}
	for _, f := range files {
		data, err := os.ReadFile(filepath.Join(from, filepath.FromSlash(f)))
		if err != nil {
			return err
		}
		target := filepath.Join(to, filepath.FromSlash(f))
		if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(target, data, 0o644); err != nil {
			return err
		}
	}
	return nil
}

func addLine(file, line string) error {
	if err := os.MkdirAll(filepath.Dir(file), 0o755); err != nil {
		return err
	}
	data, err := os.ReadFile(file)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(data) > 0 && data[len(data)-1] != '\n' {
		data = append(data, '\n')
	}
	data = append(data, line...)
	data = append(data, '\n')
	return os.WriteFile(file, data, 0o644)
}
