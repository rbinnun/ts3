package main

import (
	"bytes"
	"context"
	"encoding/json"
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

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/parse/gen"
	"github.com/antlr4-go/antlr/v4"
)

type found struct {
	field string
	value ast.Constant
}

type world struct {
	folder  string
	effects []string
	model   factstore.FactStore
	decls   map[ast.PredicateSym]*ast.Decl
}

type tool struct {
	looksAtTheModel bool
	use             func(w world, input ast.Constant) ([]found, error)
}

var tools = map[string]tool{
	"list":           {use: list},
	"count lines":    {use: countLines},
	"find comments":  {use: findComments},
	"parse":          {use: parseFile},
	"read a rule":    {use: readRule},
	"see what fired": {use: seeWhatFired, looksAtTheModel: true},
	"try":            {use: try},
}

func text(c ast.Constant) (string, error) {
	if c.Type != ast.StringType {
		return "", fmt.Errorf("%v is not a string", c)
	}
	return c.StringValue()
}

func texts(c ast.Constant) ([]string, error) {
	seq, err := c.ListSeq()
	if err != nil {
		return nil, fmt.Errorf("%v is not a list", c)
	}
	var out []string
	for item := range seq {
		s, err := text(item)
		if err != nil {
			return nil, err
		}
		out = append(out, s)
	}
	return out, nil
}

func list(w world, input ast.Constant) ([]found, error) {
	dir, err := text(input)
	if err != nil {
		return nil, err
	}
	entries, err := os.ReadDir(filepath.Join(w.folder, dir))
	if err != nil {
		return nil, err
	}
	var out []found
	for _, entry := range entries {
		out = append(out, found{"file", ast.String(filepath.Join(dir, entry.Name()))})
	}
	return out, nil
}

func countLines(w world, input ast.Constant) ([]found, error) {
	path, err := text(input)
	if err != nil {
		return nil, err
	}
	info, err := os.Stat(filepath.Join(w.folder, path))
	if err != nil {
		return nil, err
	}
	if info.IsDir() {
		return nil, nil
	}
	src, err := os.ReadFile(filepath.Join(w.folder, path))
	if err != nil {
		return nil, err
	}
	lines := bytes.Count(src, []byte("\n"))
	if len(src) > 0 && src[len(src)-1] != '\n' {
		lines++
	}
	return []found{{"lines", ast.Number(int64(lines))}}, nil
}

var commentFinders = map[string]func(src string) []string{
	"mangle": mangleComments,
	"go":     goComments,
	"sh":     shComments,
}

func findComments(w world, input ast.Constant) ([]found, error) {
	args, err := texts(input)
	if err != nil {
		return nil, err
	}
	if len(args) != 2 {
		return nil, fmt.Errorf("finding comments needs a path and a language, not %v", input)
	}
	path, language := args[0], args[1]
	finder, ok := commentFinders[language]
	if !ok {
		return nil, fmt.Errorf("there is no way to find comments written in %s", language)
	}
	src, err := os.ReadFile(filepath.Join(w.folder, path))
	if err != nil {
		return nil, err
	}
	var out []found
	for _, comment := range finder(string(src)) {
		out = append(out, found{"comment", ast.String(comment)})
	}
	return out, nil
}

type chunk struct {
	text   string
	isDecl bool
	whole  bool
}

func mangleTokens(src string) []antlr.Token {
	lexer := gen.NewMangleLexer(antlr.NewInputStream(src))
	lexer.RemoveErrorListeners()
	return lexer.GetAllTokens()
}

func mangleComments(src string) []string {
	var out []string
	for _, t := range mangleTokens(src) {
		if t.GetTokenType() == gen.MangleLexerCOMMENT {
			out = append(out, strings.TrimSpace(t.GetText()))
		}
	}
	return out
}

func chunksOf(src string) []chunk {
	runes := []rune(src)
	var out []chunk
	start, first := -1, 0
	for _, t := range mangleTokens(src) {
		if t.GetChannel() != antlr.TokenDefaultChannel {
			continue
		}
		if start < 0 {
			start, first = t.GetStart(), t.GetTokenType()
		}
		if t.GetTokenType() == gen.MangleLexerT__1 {
			out = append(out, chunk{string(runes[start : t.GetStop()+1]), first == gen.MangleLexerDECL, true})
			start = -1
		}
	}
	if start >= 0 {
		out = append(out, chunk{strings.TrimSpace(string(runes[start:])), first == gen.MangleLexerDECL, false})
	}
	return out
}

func goComments(src string) []string {
	fset := token.NewFileSet()
	file := fset.AddFile("", fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, []byte(src), nil, scanner.ScanComments)
	var out []string
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			return out
		}
		if tok == token.COMMENT {
			out = append(out, strings.TrimSpace(lit))
		}
	}
}

func shComments(src string) []string {
	var out []string
	single, double, wordStart := false, false, true
	for i := 0; i < len(src); i++ {
		c := src[i]
		switch {
		case single:
			single = c != '\''
			continue
		case double:
			if c == '\\' {
				i++
			}
			double = c != '"'
			continue
		case c == '\\':
			i++
			wordStart = false
			continue
		case c == '\'':
			single = true
		case c == '"':
			double = true
		case c == '#' && wordStart:
			end := strings.IndexByte(src[i:], '\n')
			if end < 0 {
				end = len(src) - i
			}
			out = append(out, strings.TrimSpace(src[i:i+end]))
			i += end - 1
			continue
		}
		wordStart = strings.IndexByte(" \t\n;&|()<>", c) >= 0
	}
	return out
}

func parseFile(w world, input ast.Constant) ([]found, error) {
	path, err := text(input)
	if err != nil {
		return nil, err
	}
	src, err := os.ReadFile(filepath.Join(w.folder, path))
	if err != nil {
		return nil, err
	}
	var out []found
	for _, c := range chunksOf(string(src)) {
		if !c.isDecl {
			out = append(out, found{"rule", ast.String(c.text)})
		}
	}
	return out, nil
}

func oneClause(src string) (ast.Clause, error) {
	unit, err := parse.Unit(strings.NewReader(src))
	if err != nil {
		return ast.Clause{}, err
	}
	if len(unit.Clauses) != 1 {
		return ast.Clause{}, fmt.Errorf("%q is not one rule", src)
	}
	return unit.Clauses[0], nil
}

func readRule(w world, input ast.Constant) ([]found, error) {
	src, err := text(input)
	if err != nil {
		return nil, err
	}
	clause, err := oneClause(src)
	if err != nil {
		return nil, err
	}
	out := []found{{"head", ast.String(clause.Head.Predicate.Symbol)}}
	if len(clause.Head.Args) > 0 {
		if first, ok := clause.Head.Args[0].(ast.Constant); ok {
			out = append(out, found{"first", first})
		}
	}
	for _, premise := range clause.Premises {
		var used ast.PredicateSym
		switch p := premise.(type) {
		case ast.Atom:
			used = p.Predicate
		case ast.NegAtom:
			used = p.Atom.Predicate
		default:
			continue
		}
		if !used.IsBuiltin() {
			out = append(out, found{"uses", ast.String(used.Symbol)})
		}
	}
	return out, nil
}

func seeWhatFired(w world, input ast.Constant) ([]found, error) {
	path, err := text(input)
	if err != nil {
		return nil, err
	}
	src, err := os.ReadFile(filepath.Join(w.folder, path))
	if err != nil {
		return nil, err
	}
	probe := "fired"
	for taken := true; taken; {
		taken = false
		for sym := range w.decls {
			if sym.Symbol == probe {
				probe, taken = probe+"_", true
			}
		}
	}
	var out []found
	var probes []ast.Clause
	var rules []string
	for _, c := range chunksOf(string(src)) {
		if c.isDecl || !c.whole {
			continue
		}
		clause, err := oneClause(c.text)
		if err != nil {
			return nil, err
		}
		if len(clause.Premises) == 0 {
			out = append(out, found{"fired", ast.String(c.text)})
			continue
		}
		probes = append(probes, ast.NewClause(ast.NewAtom(probe, ast.Number(int64(len(rules)))), clause.Premises))
		rules = append(rules, c.text)
	}
	if len(probes) == 0 {
		return out, nil
	}
	known := map[ast.PredicateSym]ast.Decl{}
	for sym, decl := range w.decls {
		known[sym] = *decl
	}
	info, err := analysis.Analyze([]parse.SourceUnit{{Clauses: probes}}, known)
	if err != nil {
		return nil, err
	}
	store := factstore.NewTeeingStore(w.model)
	if err := engine.EvalProgram(info, store); err != nil {
		return nil, err
	}
	err = store.Out.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: probe, Arity: 1}), func(a ast.Atom) error {
		n, err := a.Args[0].(ast.Constant).NumberValue()
		if err != nil {
			return err
		}
		out = append(out, found{"fired", ast.String(rules[n])})
		return nil
	})
	return out, err
}

func try(w world, input ast.Constant) ([]found, error) {
	args, err := texts(input)
	if err != nil {
		return nil, err
	}
	if len(args) != 3 {
		return nil, fmt.Errorf("trying a change needs a file, a line and an entry point, not %v", input)
	}
	file, line, entry := args[0], args[1], args[2]
	dir, err := os.MkdirTemp("", "a-change-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(dir)
	if err := copyFolder(w.folder, dir); err != nil {
		return nil, err
	}
	if err := addLine(filepath.Join(dir, file), line); err != nil {
		return nil, err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "sh", append([]string{entry}, w.effects...)...)
	cmd.Dir = dir
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	ran := cmd.Run()
	answer, facts, ok := heardInMangle(stdout.String())
	if !ok {
		answer, facts, ok = heardInJSON(stdout.Bytes())
	}
	if !ok {
		return nil, fmt.Errorf("the changed folder gave no answer (%v): %s", ran, strings.TrimSpace(stderr.String()))
	}
	out := []found{{"answer", ast.String(answer)}}
	for _, row := range facts["violation"] {
		if len(row) == 0 {
			continue
		}
		if _, err := text(row[0]); err == nil {
			out = append(out, found{"broke", row[0]})
		}
	}
	for _, row := range facts["unfired"] {
		if len(row) != 2 {
			continue
		}
		_, err1 := text(row[0])
		_, err2 := text(row[1])
		if err1 == nil && err2 == nil {
			fst, snd := row[0], row[1]
			out = append(out, found{"unfired", ast.Pair(&fst, &snd)})
		}
	}
	return out, nil
}

func heardInMangle(said string) (string, map[string][][]ast.Constant, bool) {
	unit, err := parse.Unit(strings.NewReader(said))
	if err != nil {
		return "", nil, false
	}
	facts := map[string][][]ast.Constant{}
	for _, clause := range unit.Clauses {
		if len(clause.Premises) > 0 || clause.Transform != nil {
			return "", nil, false
		}
		row := make([]ast.Constant, len(clause.Head.Args))
		for i, arg := range clause.Head.Args {
			row[i], _ = arg.(ast.Constant)
		}
		facts[clause.Head.Predicate.Symbol] = append(facts[clause.Head.Predicate.Symbol], row)
	}
	answers := facts["answer"]
	if len(answers) != 1 || len(answers[0]) != 1 {
		return "", nil, false
	}
	answer, err := text(answers[0][0])
	if err != nil || answer == "" {
		return "", nil, false
	}
	return answer, facts, true
}

func heardInJSON(said []byte) (string, map[string][][]ast.Constant, bool) {
	var heard struct {
		Answer string             `json:"answer"`
		Facts  map[string][][]any `json:"facts"`
	}
	if err := json.Unmarshal(said, &heard); err != nil || heard.Answer == "" {
		return "", nil, false
	}
	facts := map[string][][]ast.Constant{}
	for name, rows := range heard.Facts {
		for _, row := range rows {
			consts := make([]ast.Constant, len(row))
			for i, value := range row {
				if s, ok := value.(string); ok {
					consts[i] = ast.String(s)
				}
			}
			facts[name] = append(facts[name], consts)
		}
	}
	return heard.Answer, facts, true
}

func copyFolder(from, to string) error {
	return filepath.WalkDir(from, func(path string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(from, path)
		if err != nil {
			return err
		}
		target := filepath.Join(to, rel)
		info, err := os.Stat(path)
		if err != nil {
			return err
		}
		if info.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		return os.WriteFile(target, src, info.Mode().Perm())
	})
}

func addLine(path, line string) error {
	mode := fs.FileMode(0o644)
	if info, err := os.Stat(path); err == nil {
		mode = info.Mode().Perm()
	}
	src, err := os.ReadFile(path)
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	if len(src) > 0 && src[len(src)-1] != '\n' {
		src = append(src, '\n')
	}
	src = append(src, line+"\n"...)
	return os.WriteFile(path, src, mode)
}
