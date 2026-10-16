package main

import (
	"errors"
	"fmt"
	"sort"
	"strings"

	antlr "github.com/antlr4-go/antlr/v4"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/parse/gen"
)

var kinds = map[string]bool{"list": true, "read": true, "parse": true, "start": true, "trace": true}

type placed struct {
	line int
	text string
}

func linesOf(content string) []string {
	if content == "" {
		return nil
	}
	return strings.Split(strings.TrimSuffix(content, "\n"), "\n")
}

func parseText(text string) (parse.SourceUnit, []placed, error) {
	unit, err := parse.Unit(strings.NewReader(text))
	if err != nil {
		return parse.SourceUnit{}, nil, err
	}
	lexer := gen.NewMangleLexer(antlr.NewInputStream(text))
	lexer.RemoveErrorListeners()
	parser := gen.NewMangleParser(antlr.NewCommonTokenStream(lexer, antlr.TokenDefaultChannel))
	parser.RemoveErrorListeners()
	runes := []rune(text)
	var places []placed
	for _, clause := range parser.Start_().Program().AllClause() {
		first, last := clause.GetStart(), clause.GetStop()
		place := placed{line: first.GetLine()}
		if last != nil {
			if from, to := first.GetStart(), last.GetStop(); from >= 0 && from <= to && to < len(runes) {
				place.text = string(runes[from : to+1])
			}
		}
		places = append(places, place)
	}
	if len(places) != len(unit.Clauses) {
		return parse.SourceUnit{}, nil, errors.New("the clauses of the program could not be placed on lines")
	}
	return unit, places, nil
}

func firedIn(p *program, store factstore.FactStore) []site {
	fired := append([]site(nil), p.facts...)
	for name, place := range p.markers {
		if store.Contains(ast.NewAtom(name)) {
			fired = append(fired, place)
		}
	}
	sort.Slice(fired, func(i, j int) bool {
		if fired[i].path != fired[j].path {
			return fired[i].path < fired[j].path
		}
		return fired[i].number < fired[j].number
	})
	return fired
}

func do(s step, w world, start string, p *program, store factstore.FactStore) ([]ast.Atom, error) {
	var got []ast.Atom
	give := func(field string, value ast.Constant) {
		got = append(got, ast.NewAtom("got", s.doing, ast.String(field), value))
	}
	switch s.kind {
	case "list":
		for _, path := range w.paths() {
			give("file", ast.String(path))
		}
	case "read":
		path, err := s.one("path")
		if err != nil {
			return nil, err
		}
		content, ok := w[path]
		if !ok {
			return nil, nil
		}
		lines := linesOf(content)
		for i, line := range lines {
			give("line", ast.List([]ast.Constant{ast.Number(int64(i + 1)), ast.String(line)}))
		}
		give("lines", ast.Number(int64(len(lines))))
	case "parse":
		path, err := s.one("path")
		if err != nil {
			return nil, err
		}
		content, ok := w[path]
		if !ok {
			return nil, nil
		}
		unit, places, err := parseText(content)
		if err != nil {
			return nil, nil
		}
		for i, clause := range unit.Clauses {
			number := ast.Number(int64(i + 1))
			line := ast.Number(int64(places[i].line))
			give("clause", ast.List([]ast.Constant{number, line, ast.String(clause.Head.Predicate.Symbol)}))
			for j, arg := range clause.Head.Args {
				if c, ok := arg.(ast.Constant); ok {
					give("argument", ast.List([]ast.Constant{number, ast.Number(int64(j + 1)), c}))
				}
			}
		}
	case "start":
		var additions [][2]string
		for _, value := range s.gives["adds"] {
			items := listOf(value)
			if len(items) != 2 {
				return nil, fmt.Errorf("%s adds something that is not a path and a line: %v", s.key, value)
			}
			path, err1 := items[0].StringValue()
			line, err2 := items[1].StringValue()
			if err1 != nil || err2 != nil {
				return nil, fmt.Errorf("%s adds something that is not a path and a line: %v", s.key, value)
			}
			additions = append(additions, [2]string{path, line})
		}
		sort.Slice(additions, func(i, j int) bool {
			if additions[i][0] != additions[j][0] {
				return additions[i][0] < additions[j][0]
			}
			return additions[i][1] < additions[j][1]
		})
		o := run(w.with(additions), start, []string{s.effect})
		give("exit code", ast.Number(int64(o.code)))
		for _, atom := range o.outputs {
			fact := []ast.Constant{ast.String(atom.Predicate.Symbol)}
			for _, arg := range atom.Args {
				fact = append(fact, constantOf(arg))
			}
			give("output", ast.List(fact))
		}
		for _, place := range o.fired {
			give("fired", ast.List([]ast.Constant{ast.String(place.path), ast.Number(int64(place.number))}))
		}
	case "trace":
		for _, place := range firedIn(p, store) {
			give("fired", ast.List([]ast.Constant{ast.String(place.path), ast.Number(int64(place.number))}))
		}
	}
	return got, nil
}
