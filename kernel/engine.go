package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode"
	"unicode/utf8"

	_ "modernc.org/sqlite"
)

type Value struct {
	Num bool
	N   int64
	S   string
}

func Str(s string) Value { return Value{S: s} }

func Int(n int64) Value { return Value{Num: true, N: n} }

func (v Value) Text() string {
	if v.Num {
		return strconv.FormatInt(v.N, 10)
	}
	return v.S
}

var numberShape = regexp.MustCompile(`^-?(0|[1-9][0-9]*)$`)
var blankShape = regexp.MustCompile(`^\[([^\[\]]+)\]$`)

func readNumber(s string) (int64, bool) {
	if !numberShape.MatchString(s) {
		return 0, false
	}
	n, err := strconv.ParseInt(s, 10, 64)
	return n, err == nil
}

func plainValue(s string) Value {
	if n, ok := readNumber(s); ok {
		return Int(n)
	}
	return Str(s)
}

type Term struct {
	Blank string
	Val   Value
}

func (t Term) IsBlank() bool { return t.Blank != "" }

func (t Term) isText() bool { return !t.IsBlank() && !t.Val.Num }

type Atom struct {
	Pred string
	Args []Term
}

func predKey(pred string, arity int) string { return pred + "/" + strconv.Itoa(arity) }

func (a Atom) Key() string { return predKey(a.Pred, len(a.Args)) }

func (a Atom) tuple() []Value {
	t := make([]Value, len(a.Args))
	for i, x := range a.Args {
		t[i] = x.Val
	}
	return t
}

func fact(pred string, vals ...Value) Atom {
	a := Atom{Pred: pred, Args: make([]Term, len(vals))}
	for i, v := range vals {
		a.Args[i] = Term{Val: v}
	}
	return a
}

type part struct {
	text   string
	quoted bool
}

func splitParts(line string) ([]part, error) {
	var parts []part
	i := 0
	for {
		if i < len(line) && (line[i] == '"' || line[i] == '\'') {
			q := line[i]
			var b strings.Builder
			j := i + 1
			closed := false
			for j < len(line) {
				if line[j] == q {
					if j+1 < len(line) && line[j+1] == q {
						b.WriteByte(q)
						j += 2
						continue
					}
					closed = true
					j++
					break
				}
				b.WriteByte(line[j])
				j++
			}
			if !closed {
				return nil, errors.New("a quoted value has no closing quote")
			}
			parts = append(parts, part{b.String(), true})
			if j == len(line) {
				return parts, nil
			}
			if !strings.HasPrefix(line[j:], ", ") {
				return nil, errors.New("a quoted value is not followed by a comma and a space")
			}
			i = j + 2
			continue
		}
		k := strings.Index(line[i:], ", ")
		if k < 0 {
			return append(parts, part{line[i:], false}), nil
		}
		parts = append(parts, part{line[i : i+k], false})
		i += k + 2
	}
}

func partTerm(p part) Term {
	if p.quoted {
		return Term{Val: Str(p.text)}
	}
	if m := blankShape.FindStringSubmatch(p.text); m != nil {
		return Term{Blank: m[1]}
	}
	return Term{Val: plainValue(p.text)}
}

func isWords(p part, t Term) bool {
	return !p.quoted && t.isText() && p.text != ""
}

func parseAtom(line string) (Atom, error) {
	parts, err := splitParts(line)
	if err != nil {
		return Atom{}, err
	}
	terms := make([]Term, len(parts))
	for i, p := range parts {
		terms[i] = partTerm(p)
	}
	switch len(parts) {
	case 1:
		if !isWords(parts[0], terms[0]) {
			return Atom{}, errors.New("a line of one part must be plain words")
		}
		return Atom{Pred: parts[0].text}, nil
	case 2:
		return Atom{}, errors.New("a line must have one part or at least three")
	}
	if !isWords(parts[1], terms[1]) {
		return Atom{}, errors.New("the second part of a line must be plain words")
	}
	if parts[1].text == "is" && len(parts) == 3 && isWords(parts[2], terms[2]) {
		return Atom{Pred: parts[2].text, Args: []Term{terms[0]}}, nil
	}
	args := append([]Term{terms[0]}, terms[2:]...)
	return Atom{Pred: parts[1].text, Args: args}, nil
}

func readCell(text string) Value {
	if parts, err := splitParts(text); err == nil && len(parts) == 1 && parts[0].quoted {
		return Str(parts[0].text)
	}
	return plainValue(text)
}

func needsQuotes(s string) bool {
	if s == "" || strings.Contains(s, ", ") || strings.ContainsAny(s, "\n\r") {
		return true
	}
	if s[0] == '"' || s[0] == '\'' || blankShape.MatchString(s) {
		return true
	}
	if _, ok := readNumber(s); ok {
		return true
	}
	first, _ := utf8.DecodeRuneInString(s)
	last, _ := utf8.DecodeLastRuneInString(s)
	return unicode.IsSpace(first) || unicode.IsSpace(last)
}

func quoteText(s string) string {
	if strings.Contains(s, `"`) && !strings.Contains(s, "'") {
		return "'" + s + "'"
	}
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func renderValue(v Value, force bool) string {
	if v.Num {
		return strconv.FormatInt(v.N, 10)
	}
	if force || needsQuotes(v.S) {
		return quoteText(v.S)
	}
	return v.S
}

func renderTerm(t Term, force bool) string {
	if t.IsBlank() {
		return "[" + t.Blank + "]"
	}
	return renderValue(t.Val, force)
}

func renderAtom(a Atom, guardNot bool) string {
	n := len(a.Args)
	if n == 0 {
		return a.Pred
	}
	head := a.Args[0]
	first := renderTerm(head, guardNot && head.isText() && strings.HasPrefix(head.Val.S, "not "))
	if n == 1 {
		return first + ", is, " + a.Pred
	}
	var b strings.Builder
	b.WriteString(first)
	b.WriteString(", ")
	b.WriteString(a.Pred)
	for i, t := range a.Args[1:] {
		b.WriteString(", ")
		b.WriteString(renderTerm(t, a.Pred == "is" && n == 2 && i == 0 && t.isText()))
	}
	return b.String()
}

func renderCondition(a Atom, neg bool) string {
	if neg {
		return "not " + renderAtom(a, false)
	}
	return renderAtom(a, true)
}

type Cond struct {
	Atom Atom
	Neg  bool
}

type Rule struct {
	Name  string
	File  string
	Line  int
	Lines []string
	Head  Atom
	Conds []Cond
}

func (r *Rule) render() []string {
	out := []string{renderAtom(r.Head, false)}
	for i, c := range r.Conds {
		word := "    if "
		if i > 0 {
			word = "    and "
		}
		out = append(out, word+renderCondition(c.Atom, c.Neg))
	}
	return out
}

func (r *Rule) text() string { return strings.Join(r.Lines, "\n") }

func (r *Rule) id() string { return shortHash(r.text()) }

func (r *Rule) place() string { return fmt.Sprintf("%s:%d", r.File, r.Line) }

func (r *Rule) isFact() bool {
	if len(r.Conds) > 0 {
		return false
	}
	for _, t := range r.Head.Args {
		if t.IsBlank() {
			return false
		}
	}
	return true
}

func parsePlain(file, data string) ([]*Rule, error) {
	lines := strings.Split(data, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var rules []*Rule
	var cur *Rule
	for i, line := range lines {
		no := i + 1
		where := func(err error) error { return fmt.Errorf("%s:%d: %v", file, no, err) }
		if strings.TrimSpace(line) == "" {
			cur = nil
			continue
		}
		if strings.HasPrefix(line, " ") {
			if cur == nil {
				return nil, where(errors.New("a condition has no rule above it"))
			}
			var rest string
			switch {
			case strings.HasPrefix(line, "    if "):
				if len(cur.Conds) > 0 {
					return nil, where(errors.New("only the first condition starts with if"))
				}
				rest = line[len("    if "):]
			case strings.HasPrefix(line, "    and "):
				if len(cur.Conds) == 0 {
					return nil, where(errors.New("the first condition starts with if"))
				}
				rest = line[len("    and "):]
			default:
				return nil, where(errors.New("a condition starts with four spaces and if or and"))
			}
			neg := false
			if strings.HasPrefix(rest, "not ") {
				neg = true
				rest = rest[len("not "):]
			}
			a, err := parseAtom(rest)
			if err != nil {
				return nil, where(err)
			}
			cur.Conds = append(cur.Conds, Cond{Atom: a, Neg: neg})
			cur.Lines = append(cur.Lines, line)
			continue
		}
		a, err := parseAtom(line)
		if err != nil {
			return nil, where(err)
		}
		cur = &Rule{File: file, Line: no, Lines: []string{line}, Head: a}
		rules = append(rules, cur)
	}
	for _, r := range rules {
		r.Name = r.id()
	}
	return rules, nil
}

func parsePattern(p string) (Atom, bool) {
	if strings.Contains(p, ", ") || strings.TrimSpace(p) == "" {
		return Atom{}, false
	}
	type seg struct {
		blank bool
		text  string
	}
	var segs []seg
	rest := p
	for {
		i := strings.Index(rest, "[")
		if i < 0 {
			if t := strings.TrimSpace(rest); t != "" {
				segs = append(segs, seg{false, t})
			}
			break
		}
		j := strings.Index(rest[i:], "]")
		if j < 0 {
			return Atom{}, false
		}
		if t := strings.TrimSpace(rest[:i]); t != "" {
			segs = append(segs, seg{false, t})
		}
		name := rest[i+1 : i+j]
		if name == "" || strings.Contains(name, "[") {
			return Atom{}, false
		}
		segs = append(segs, seg{true, name})
		rest = rest[i+j+1:]
	}
	term := func(s seg) Term {
		if s.blank {
			return Term{Blank: s.text}
		}
		return Term{Val: plainValue(s.text)}
	}
	switch {
	case len(segs) == 1 && !segs[0].blank:
		return Atom{Pred: segs[0].text}, true
	case len(segs) == 2 && segs[0].blank && !segs[1].blank && strings.HasPrefix(segs[1].text, "is "):
		return Atom{Pred: strings.TrimSpace(segs[1].text[3:]), Args: []Term{term(segs[0])}}, true
	case len(segs) >= 3 && !segs[1].blank:
		args := []Term{term(segs[0])}
		for _, s := range segs[2:] {
			args = append(args, term(s))
		}
		return Atom{Pred: segs[1].text, Args: args}, true
	}
	return Atom{}, false
}

func shortHash(s string) string {
	h := sha256.Sum256([]byte(s))
	return hex.EncodeToString(h[:])[:16]
}

func hashFile(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	h := sha256.Sum256(data)
	return hex.EncodeToString(h[:]), nil
}

type Rel struct {
	tuples [][]Value
	seen   map[string]bool
	index  map[int]map[Value][]int
}

func tupleKey(t []Value) string {
	var b strings.Builder
	for _, v := range t {
		if v.Num {
			b.WriteByte('n')
			b.WriteString(strconv.FormatInt(v.N, 10))
		} else {
			b.WriteByte('s')
			b.WriteString(v.S)
		}
		b.WriteByte(0)
	}
	return b.String()
}

func (r *Rel) lookup(p int, v Value) []int {
	if r.index == nil {
		r.index = map[int]map[Value][]int{}
	}
	ix := r.index[p]
	if ix == nil {
		ix = map[Value][]int{}
		for n, t := range r.tuples {
			ix[t[p]] = append(ix[t[p]], n)
		}
		r.index[p] = ix
	}
	return ix[v]
}

type DB struct {
	rels   map[string]*Rel
	preds  map[string]string
	keys   []string
	origin map[string]string
}

func newDB() *DB {
	return &DB{rels: map[string]*Rel{}, preds: map[string]string{}, origin: map[string]string{}}
}

func (db *DB) add(pred string, t []Value) bool {
	k := predKey(pred, len(t))
	r := db.rels[k]
	if r == nil {
		r = &Rel{seen: map[string]bool{}}
		db.rels[k] = r
		db.preds[k] = pred
		db.keys = append(db.keys, k)
	}
	tk := tupleKey(t)
	if r.seen[tk] {
		return false
	}
	r.seen[tk] = true
	r.tuples = append(r.tuples, t)
	n := len(r.tuples) - 1
	for p, ix := range r.index {
		ix[t[p]] = append(ix[t[p]], n)
	}
	return true
}

func (db *DB) addFact(a Atom, origin string) {
	t := a.tuple()
	db.add(a.Pred, t)
	if origin != "" {
		ok := a.Key() + "\x01" + tupleKey(t)
		if _, seen := db.origin[ok]; !seen {
			db.origin[ok] = origin
		}
	}
}

func (db *DB) originOf(key string, t []Value) string {
	if o, ok := db.origin[key+"\x01"+tupleKey(t)]; ok {
		return o
	}
	return "derived"
}

func (db *DB) has(a Atom) bool {
	r := db.rels[a.Key()]
	if r == nil {
		return false
	}
	ids := map[string]int{}
	var ss []slot
	for _, t := range a.Args {
		if !t.IsBlank() {
			ss = append(ss, slot{v: -1, c: t.Val})
			continue
		}
		id, ok := ids[t.Blank]
		if !ok {
			id = len(ids)
			ids[t.Blank] = id
		}
		ss = append(ss, slot{v: id})
	}
	env := make([]Value, len(ids))
	bound := make([]bool, len(ids))
	return db.each(r, ss, env, bound, func() bool { return true })
}

type Binding map[string]Value

func (b Binding) text(name string) string { return b[name].Text() }

func (db *DB) ask(query string) []Binding {
	a, err := parseAtom(query)
	if err != nil {
		panic(err)
	}
	r := db.rels[a.Key()]
	if r == nil {
		return nil
	}
	var out []Binding
	for _, t := range r.tuples {
		b := Binding{}
		ok := true
		for i, x := range a.Args {
			if !x.IsBlank() {
				if t[i] != x.Val {
					ok = false
					break
				}
				continue
			}
			if old, seen := b[x.Blank]; seen && old != t[i] {
				ok = false
				break
			}
			b[x.Blank] = t[i]
		}
		if ok {
			out = append(out, b)
		}
	}
	return out
}

type slot struct {
	v int
	c Value
}

type lit struct {
	key     string
	args    []slot
	neg     bool
	builtin *Builtin
}

type plan struct {
	rule  *Rule
	key   string
	head  []slot
	body  []lit
	conds []lit
	names []string
}

func (db *DB) each(r *Rel, args []slot, env []Value, bound []bool, k func() bool) bool {
	var cand []int
	all := true
	for j, s := range args {
		if s.v < 0 {
			cand, all = r.lookup(j, s.c), false
			break
		}
		if bound[s.v] {
			cand, all = r.lookup(j, env[s.v]), false
			break
		}
	}
	n := len(r.tuples)
	if !all {
		n = len(cand)
	}
	var fresh []int
	for x := 0; x < n; x++ {
		t := r.tuples[x]
		if !all {
			t = r.tuples[cand[x]]
		}
		ok := true
		fresh = fresh[:0]
		for j, s := range args {
			switch {
			case s.v < 0:
				ok = t[j] == s.c
			case bound[s.v]:
				ok = env[s.v] == t[j]
			default:
				env[s.v] = t[j]
				bound[s.v] = true
				fresh = append(fresh, s.v)
			}
			if !ok {
				break
			}
		}
		stop := false
		if ok {
			stop = k()
		}
		for _, v := range fresh {
			bound[v] = false
		}
		if stop {
			return true
		}
	}
	return false
}

func (db *DB) solve(p *plan, i int, env []Value, bound []bool, emit func()) {
	if i == len(p.body) {
		emit()
		return
	}
	l := &p.body[i]
	if l.builtin != nil {
		ok, v, val := l.builtin.eval(l.args, env, bound)
		if l.neg {
			if !ok {
				db.solve(p, i+1, env, bound, emit)
			}
			return
		}
		if !ok {
			return
		}
		if v >= 0 && !bound[v] {
			env[v] = val
			bound[v] = true
			db.solve(p, i+1, env, bound, emit)
			bound[v] = false
			return
		}
		db.solve(p, i+1, env, bound, emit)
		return
	}
	r := db.rels[l.key]
	if l.neg {
		if r == nil || !db.each(r, l.args, env, bound, func() bool { return true }) {
			db.solve(p, i+1, env, bound, emit)
		}
		return
	}
	if r == nil {
		return
	}
	db.each(r, l.args, env, bound, func() bool {
		db.solve(p, i+1, env, bound, emit)
		return false
	})
}

func ground(ss []slot, env []Value) []Value {
	out := make([]Value, len(ss))
	for i, s := range ss {
		if s.v < 0 {
			out[i] = s.c
		} else {
			out[i] = env[s.v]
		}
	}
	return out
}

type bterm struct {
	pos int
	val Value
}

type Builtin struct {
	op   string
	name string
	args []bterm
	out  bterm
	text string
	vars map[string]int
}

func (b *Builtin) positions(neg bool) []int {
	var ps []int
	for _, a := range b.args {
		if a.pos >= 0 {
			ps = append(ps, a.pos)
		}
	}
	if b.op == "fn" && neg && b.out.pos >= 0 {
		ps = append(ps, b.out.pos)
	}
	return ps
}

func (b *Builtin) needs(args []slot, neg bool) []int {
	var vs []int
	for _, p := range b.positions(neg) {
		if args[p].v >= 0 {
			vs = append(vs, args[p].v)
		}
	}
	return vs
}

func (b *Builtin) output(args []slot) int {
	if b.op != "fn" || b.out.pos < 0 {
		return -1
	}
	return args[b.out.pos].v
}

func (b *Builtin) value(t bterm, args []slot, env []Value) Value {
	if t.pos < 0 {
		return t.val
	}
	s := args[t.pos]
	if s.v < 0 {
		return s.c
	}
	return env[s.v]
}

func (b *Builtin) eval(args []slot, env []Value, bound []bool) (bool, int, Value) {
	vals := make([]Value, len(b.args))
	for i, a := range b.args {
		vals[i] = b.value(a, args, env)
	}
	switch b.op {
	case "!=":
		return vals[0] != vals[1], -1, Value{}
	case "=":
		return vals[0] == vals[1], -1, Value{}
	case "call":
		return callBuiltin(b.name, vals), -1, Value{}
	case "fn":
		res, ok := applyFunction(b.name, vals)
		if !ok {
			return false, -1, Value{}
		}
		if b.out.pos < 0 {
			return res == b.out.val, -1, Value{}
		}
		s := args[b.out.pos]
		if s.v < 0 {
			return res == s.c, -1, Value{}
		}
		if bound[s.v] {
			return res == env[s.v], -1, Value{}
		}
		return true, s.v, res
	}
	return false, -1, Value{}
}

var knownCalls = map[string]bool{":string:starts_with": true, ":string:ends_with": true, ":string:contains": true, ":lt": true, ":le": true, ":gt": true, ":ge": true}
var knownFunctions = map[string]bool{"fn:plus": true, "fn:minus": true, "fn:mult": true, "fn:string:concat": true}

func callBuiltin(name string, v []Value) bool {
	if len(v) != 2 {
		return false
	}
	switch name {
	case ":string:starts_with", ":string:ends_with", ":string:contains":
		if v[0].Num || v[1].Num {
			return false
		}
		switch name {
		case ":string:starts_with":
			return strings.HasPrefix(v[0].S, v[1].S)
		case ":string:ends_with":
			return strings.HasSuffix(v[0].S, v[1].S)
		}
		return strings.Contains(v[0].S, v[1].S)
	case ":lt", ":le", ":gt", ":ge":
		if !v[0].Num || !v[1].Num {
			return false
		}
		a, c := v[0].N, v[1].N
		switch name {
		case ":lt":
			return a < c
		case ":le":
			return a <= c
		case ":gt":
			return a > c
		}
		return a >= c
	}
	return false
}

func applyFunction(name string, v []Value) (Value, bool) {
	switch name {
	case "fn:string:concat":
		var b strings.Builder
		for _, x := range v {
			b.WriteString(x.Text())
		}
		return Str(b.String()), true
	case "fn:plus", "fn:minus", "fn:mult":
		if len(v) == 0 {
			return Value{}, false
		}
		for _, x := range v {
			if !x.Num {
				return Value{}, false
			}
		}
		n := v[0].N
		for _, x := range v[1:] {
			switch name {
			case "fn:plus":
				n += x.N
			case "fn:minus":
				n -= x.N
			default:
				n *= x.N
			}
		}
		return Int(n), true
	}
	return Value{}, false
}

type mtoken struct {
	kind string
	text string
	val  Value
}

func mangleTokens(s string) ([]mtoken, error) {
	var out []mtoken
	i := 0
	for i < len(s) {
		c := s[i]
		switch {
		case c == ' ':
			i++
		case c == '(' || c == ')' || c == ',':
			out = append(out, mtoken{kind: string(c)})
			i++
		case c == '!' && i+1 < len(s) && s[i+1] == '=':
			out = append(out, mtoken{kind: "!="})
			i += 2
		case c == '=':
			out = append(out, mtoken{kind: "="})
			i++
		case c == '"':
			j := i + 1
			var b strings.Builder
			for j < len(s) && s[j] != '"' {
				if s[j] == '\\' && j+1 < len(s) {
					j++
					switch s[j] {
					case 'n':
						b.WriteByte('\n')
					default:
						b.WriteByte(s[j])
					}
					j++
					continue
				}
				b.WriteByte(s[j])
				j++
			}
			if j >= len(s) {
				return nil, errors.New("a string has no closing quote")
			}
			out = append(out, mtoken{kind: "value", val: Str(b.String())})
			i = j + 1
		case c == '-' || (c >= '0' && c <= '9'):
			j := i + 1
			for j < len(s) && s[j] >= '0' && s[j] <= '9' {
				j++
			}
			n, ok := readNumber(s[i:j])
			if !ok {
				return nil, fmt.Errorf("%q is not a number", s[i:j])
			}
			out = append(out, mtoken{kind: "value", val: Int(n)})
			i = j
		case c == ':' || c == '_' || unicode.IsLetter(rune(c)):
			j := i + 1
			for j < len(s) && (s[j] == ':' || s[j] == '_' || unicode.IsLetter(rune(s[j])) || unicode.IsDigit(rune(s[j]))) {
				j++
			}
			out = append(out, mtoken{kind: "name", text: s[i:j]})
			i = j
		default:
			return nil, fmt.Errorf("%q cannot be read", string(c))
		}
	}
	return out, nil
}

func parseMangle(text string, vars map[string]int) (*Builtin, error) {
	toks, err := mangleTokens(text)
	if err != nil {
		return nil, err
	}
	i := 0
	peek := func() mtoken {
		if i < len(toks) {
			return toks[i]
		}
		return mtoken{kind: "end"}
	}
	operand := func() (bterm, error) {
		t := peek()
		i++
		switch {
		case t.kind == "value":
			return bterm{pos: -1, val: t.val}, nil
		case t.kind == "name" && !strings.HasPrefix(t.text, ":") && !strings.HasPrefix(t.text, "fn:"):
			p, ok := vars[t.text]
			if !ok {
				return bterm{}, fmt.Errorf("%s is not a blank of the line", t.text)
			}
			return bterm{pos: p}, nil
		}
		return bterm{}, errors.New("a value or a blank is expected")
	}
	arguments := func() ([]bterm, error) {
		if peek().kind != "(" {
			return nil, errors.New("an opening bracket is expected")
		}
		i++
		var out []bterm
		for peek().kind != ")" {
			if peek().kind == "end" {
				return nil, errors.New("a closing bracket is expected")
			}
			if len(out) > 0 {
				if peek().kind != "," {
					return nil, errors.New("a comma is expected")
				}
				i++
			}
			a, err := operand()
			if err != nil {
				return nil, err
			}
			out = append(out, a)
		}
		i++
		return out, nil
	}
	b := &Builtin{text: text, vars: vars}
	switch {
	case len(toks) > 0 && toks[0].kind == "name" && strings.HasPrefix(toks[0].text, ":"):
		i++
		if !knownCalls[toks[0].text] {
			return nil, fmt.Errorf("engine.go has no %s", toks[0].text)
		}
		args, err := arguments()
		if err != nil {
			return nil, err
		}
		b.op, b.name, b.args = "call", toks[0].text, args
	case len(toks) >= 3 && toks[1].kind == "=" && toks[2].kind == "name" && strings.HasPrefix(toks[2].text, "fn:"):
		out, err := operand()
		if err != nil {
			return nil, err
		}
		i += 2
		if !knownFunctions[toks[2].text] {
			return nil, fmt.Errorf("engine.go has no %s", toks[2].text)
		}
		args, err := arguments()
		if err != nil {
			return nil, err
		}
		b.op, b.name, b.args, b.out = "fn", toks[2].text, args, out
	default:
		left, err := operand()
		if err != nil {
			return nil, err
		}
		op := peek().kind
		if op != "!=" && op != "=" {
			return nil, errors.New("a builtin, != or = is expected")
		}
		i++
		right, err := operand()
		if err != nil {
			return nil, err
		}
		b.op, b.args = op, []bterm{left, right}
	}
	if peek().kind != "end" {
		return nil, errors.New("the text goes on after the builtin")
	}
	return b, nil
}

func camel(name string) string {
	var b strings.Builder
	for _, w := range strings.Fields(name) {
		r, size := utf8.DecodeRuneInString(w)
		b.WriteRune(unicode.ToUpper(r))
		b.WriteString(w[size:])
	}
	return b.String()
}

func mangleString(s string) string {
	r := strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`)
	return `"` + r.Replace(s) + `"`
}

func mangleTerm(t Term) string {
	if t.IsBlank() {
		return camel(t.Blank)
	}
	if t.Val.Num {
		return strconv.FormatInt(t.Val.N, 10)
	}
	return mangleString(t.Val.S)
}

func mangleAtom(a Atom) string {
	args := make([]string, len(a.Args))
	for i, t := range a.Args {
		args[i] = mangleTerm(t)
	}
	return strings.ReplaceAll(a.Pred, " ", "_") + "(" + strings.Join(args, ", ") + ")"
}

func (b *Builtin) render(a Atom) string {
	var out strings.Builder
	s := b.text
	i := 0
	for i < len(s) {
		c := s[i]
		if c == '"' {
			j := i + 1
			for j < len(s) && s[j] != '"' {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			if j < len(s) {
				j++
			}
			out.WriteString(s[i:j])
			i = j
			continue
		}
		if c == ':' || c == '_' || unicode.IsLetter(rune(c)) {
			j := i + 1
			for j < len(s) && (s[j] == ':' || s[j] == '_' || unicode.IsLetter(rune(s[j])) || unicode.IsDigit(rune(s[j]))) {
				j++
			}
			word := s[i:j]
			if p, ok := b.vars[word]; ok && p < len(a.Args) {
				out.WriteString(mangleTerm(a.Args[p]))
			} else {
				out.WriteString(word)
			}
			i = j
			continue
		}
		out.WriteByte(c)
		i++
	}
	return out.String()
}

const (
	qLoads         = "[go file], loads, [file]"
	qBuildsOn      = "[level], builds on, [other level]"
	qTestedWith    = "[level], is tested with, [file]"
	qMeans         = "[ending], means, [language]"
	qLoadedAs      = "[language], is loaded as, [way]"
	qPrivate       = "[fact pattern], is, private to its level"
	qMangle        = "[line], means in mangle, [mangle]"
	qExpects       = "[level], expects, [fact]"
	qRulesOut      = "[level], rules out, [fact]"
	qShows         = "the knowledge, shows, [fact pattern]"
	qReasons       = "the knowledge, gives reasons for, [fact pattern]"
	qAnswer        = "the folder, conforms, [answer]"
	qExit          = "[answer], exits with, [code]"
	qPrints        = "[go file], prints, [knowledge]"
	qPrintsIn      = "[go file], prints in, [language]"
	qPrintsTo      = "[go file], prints to, [output]"
	qPublishedTo   = "the knowledge, is published to, [store]"
	qPublishedWhen = "the knowledge, is published only when, [answer]"
	qSqlite        = "[store], is the sqlite file, [file]"
	qTable         = "[store], has the table, [table]"
	qRowFor        = "[table], has a row for, [row]"
	qColumn        = "[table], has the column, [number], [column], [value]"
	qHolds         = "the certificate, holds, [part]"
	qComputed      = "[term], is computed as, [description]"
	qInKnowledge   = "[rule], is, in the knowledge"
	qCalls         = "[command], calls, [tool], [input]"
	qAddsLine      = "[change], adds line, [file], [line]"
	qCatalog       = "[tool], is, in the catalog"
)

var engineQueries = []string{qLoads, qBuildsOn, qTestedWith, qMeans, qLoadedAs, qPrivate, qMangle, qExpects, qRulesOut, qShows, qReasons, qAnswer, qExit, qPrints, qPrintsIn, qPrintsTo, qPublishedTo, qPublishedWhen, qSqlite, qTable, qRowFor, qColumn, qHolds, qComputed, qInKnowledge, qCalls, qAddsLine, qCatalog}

var computations = map[string]string{
	"a rule id":                     "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":                     "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a derivation id":               "the first 16 hex digits of the sha256 of the fact and the rule id and the reasons as plain lines joined by newlines",
	"a rule name":                   "the rule id",
	"a row name":                    "the file name and a colon and the line number",
	"a cell value":                  "the cell text read as a plain value",
	"a quoted value":                "a value between double quotes unless it holds a double quote and no single quote and then between single quotes",
	"a quote inside a quoted value": "the quote the value is between written twice",
	"a part of a line":              "the text between two commas that are each followed by a space",
	"a not condition":               "true when no fact matches it for any value of a blank found nowhere else in its rule",
	"a missing fact":                "a fact a level expects that the knowledge does not hold without the facts about what is missing or present",
	"a present fact":                "a fact a level rules out that the knowledge holds without the facts about what is missing or present",
	"an agent file":                 "agent.plain in a level folder which an agent writes and may rewrite on any run",
	"a level":                       "a folder next to the kernel folder named by the folder name",
	"the level being proven":        "the level whose folder runme.sh is run in",
	"a level file":                  "human.plain or agent.plain in the level folder",
	"a level store":                 "the level name followed by .db in the folder that holds the level folders",
	"a loaded level":                "the level being proven and every level a loaded level builds on where a level with no folder loads nothing",
	"a loaded file":                 "a level file of a loaded level and every file a level file says engine.go loads",
	"a tested file":                 "a file the level being proven is tested with found in its folder and loaded like a file engine.go loads",
	"a file name":                   "the path of the file from the folder that holds the level folders",
	"a proven level":                "a loaded level other than the level being proven whose store holds a certificate with the answer true and with the hash of every file it names as that file is now",
	"a certified file":              "a file loaded from the folder of a proven level",
	"a private fact":                "a fact of a private fact pattern which engine.go does not load from a certified file",
}

const (
	wayPlain = "rules and facts"
	wayRows  = "a row per line after the first with a cell for each column the first line names"
)

var ways = map[string]bool{wayPlain: true, wayRows: true}

const (
	rowRule        = "every rule"
	rowFact        = "every fact"
	rowDerive      = "every way a rule derives a fact"
	rowReason      = "every reason of every derivation"
	rowPart        = "every part the certificate holds"
	colRuleID      = "the rule id"
	colRuleFile    = "the file the rule is in"
	colRuleLine    = "the number of the line the rule starts on"
	colRuleText    = "the rule lines joined by newlines"
	colFactID      = "the fact id"
	colFactText    = "the fact as one plain line"
	colOrigin      = "the go file that observed the fact and derived for every other fact"
	colDeriveID    = "the derivation id"
	colReasonAt    = "the number of the condition in the rule"
	colReason      = "the condition with its blanks filled as one plain line"
	colPart        = "what the certificate holds"
	colSubject     = "the file a hash is of and empty otherwise"
	colPartValue   = "the sha256 of the file in hex or the level name or the answer"
	partLevel      = "the name of the level being proven"
	partLoaded     = "the hash of every file engine.go loads or the level is tested with"
	partMachine    = "the hash of every file that is part of the machine"
	partAnswer     = "the answer"
	theLevelStore  = "the level store"
	theKnowledge   = "the knowledge"
	plainLanguage  = "plain language"
	standardOutput = "standard output"
)

var rowKinds = map[string][]string{
	rowRule:   {colRuleID, colRuleFile, colRuleLine, colRuleText},
	rowFact:   {colFactID, colFactText, colOrigin},
	rowDerive: {colDeriveID, colFactID, colRuleID},
	rowReason: {colDeriveID, colReasonAt, colReason},
	rowPart:   {colPart, colSubject, colPartValue},
}

var certificateParts = map[string]bool{partLevel: true, partLoaded: true, partMachine: true, partAnswer: true}

type Source struct {
	Name      string
	Path      string
	Certified bool
	Read      bool
	Rules     []*Rule
	Rows      []Atom
}

type entry struct {
	a      Atom
	origin string
}

type Machine struct {
	change     bool
	root       string
	level      string
	levelDir   string
	machineDir string
	engineName string
	toolsName  string
	exe        string

	sources  []*Source
	rules    []*Rule
	plans    []*plan
	strata   [][]*plan
	loops    []bool
	builtins map[string]*Builtin
	levels   []string
	proven   []string
	static   []Atom

	mu          sync.Mutex
	problems    []string
	seenProblem map[string]bool
}

func (m *Machine) problem(text string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.seenProblem[text] {
		return
	}
	m.seenProblem[text] = true
	m.problems = append(m.problems, text)
}

func within(root, name string) (string, bool) {
	p := filepath.Join(root, filepath.FromSlash(name))
	rel, err := filepath.Rel(root, p)
	if err != nil || rel == "." || rel == ".." || strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
		return "", false
	}
	return p, true
}

func isDir(p string) bool {
	st, err := os.Stat(p)
	return err == nil && st.IsDir()
}

func realPath(p string) (string, error) {
	a, err := filepath.Abs(p)
	if err != nil {
		return "", err
	}
	if r, err := filepath.EvalSymlinks(a); err == nil {
		return r, nil
	}
	return a, nil
}

func (m *Machine) setup(machine string) error {
	md, err := realPath(machine)
	if err != nil {
		return err
	}
	wd, err := os.Getwd()
	if err != nil {
		return err
	}
	cwd, err := realPath(wd)
	if err != nil {
		return err
	}
	m.machineDir = md
	m.root = filepath.Dir(md)
	if filepath.Dir(cwd) != m.root {
		return fmt.Errorf("runme.sh runs in a level folder next to %s, not in %s", md, cwd)
	}
	m.level = filepath.Base(cwd)
	m.levelDir = cwd
	m.engineName = filepath.Base(md) + "/engine.go"
	m.toolsName = filepath.Base(md) + "/tools.go"
	m.exe, err = os.Executable()
	return err
}

func (m *Machine) source(name string) *Source {
	for _, s := range m.sources {
		if s.Name == name {
			return s
		}
	}
	return nil
}

func groundDB(rules []*Rule) *DB {
	db := newDB()
	for _, r := range rules {
		if r.isFact() {
			db.addFact(r.Head, "")
		}
	}
	return db
}

func (m *Machine) sourceRules() []*Rule {
	var out []*Rule
	for _, s := range m.sources {
		out = append(out, s.Rules...)
	}
	return out
}

func (m *Machine) loadLevels() error {
	seen := map[string]bool{}
	queue := []string{m.level}
	for len(queue) > 0 {
		lv := queue[0]
		queue = queue[1:]
		if seen[lv] {
			continue
		}
		seen[lv] = true
		m.levels = append(m.levels, lv)
		dir := filepath.Join(m.root, lv)
		if lv == "" || lv == "." || lv == ".." || strings.ContainsAny(lv, `/\`) || !isDir(dir) {
			continue
		}
		for _, base := range []string{"human.plain", "agent.plain"} {
			path := filepath.Join(dir, base)
			data, err := os.ReadFile(path)
			if err != nil {
				continue
			}
			name := lv + "/" + base
			rules, err := parsePlain(name, string(data))
			if err != nil {
				return err
			}
			m.sources = append(m.sources, &Source{Name: name, Path: path, Read: true, Rules: rules})
		}
		for _, b := range groundDB(m.sourceRules()).ask(qBuildsOn) {
			if seen[b.text("level")] && !seen[b.text("other level")] {
				queue = append(queue, b.text("other level"))
			}
		}
	}
	return nil
}

func (m *Machine) wayFor(g *DB, name string) string {
	best, language := "", ""
	for _, b := range g.ask(qMeans) {
		e := b.text("ending")
		if e != "" && strings.HasSuffix(name, e) && len(e) > len(best) {
			best, language = e, b.text("language")
		}
	}
	if best == "" {
		return ""
	}
	for _, b := range g.ask(qLoadedAs) {
		if b.text("language") == language && ways[b.text("way")] {
			return b.text("way")
		}
	}
	return ""
}

func (m *Machine) loadFiles() error {
	g := groundDB(m.sourceRules())
	var names []string
	for _, b := range g.ask(qLoads) {
		if b.text("go file") == m.engineName {
			names = append(names, b.text("file"))
		}
	}
	for _, b := range g.ask(qTestedWith) {
		if b.text("level") != m.level {
			continue
		}
		f := b.text("file")
		if !strings.HasPrefix(f, m.level+"/") {
			m.problem(f + " is not in the folder of " + m.level)
			continue
		}
		names = append(names, f)
	}
	for _, name := range names {
		if m.source(name) != nil {
			continue
		}
		path, ok := within(m.root, name)
		if !ok {
			m.problem(name + " is not in the folder that holds the level folders")
			continue
		}
		src := &Source{Name: name, Path: path}
		m.sources = append(m.sources, src)
		data, err := os.ReadFile(path)
		if err != nil {
			m.problem(name + " cannot be read")
			continue
		}
		switch m.wayFor(g, name) {
		case wayPlain:
			rules, err := parsePlain(name, string(data))
			if err != nil {
				return err
			}
			src.Rules = rules
		case wayRows:
			rows, err := readRows(name, data)
			if err != nil {
				m.problem(name + " cannot be read as rows: " + err.Error())
				continue
			}
			src.Rows = rows
		default:
			m.problem("engine.go does not know how to load " + name)
			continue
		}
		src.Read = true
	}
	return nil
}

func readRows(name string, data []byte) ([]Atom, error) {
	r := csv.NewReader(bytes.NewReader(data))
	r.FieldsPerRecord = -1
	header, err := r.Read()
	if err == io.EOF {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	var out []Atom
	for {
		rec, err := r.Read()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		line, _ := r.FieldPos(0)
		row := Str(fmt.Sprintf("%s:%d", name, line))
		out = append(out, fact("is a row of", row, Str(name)), fact("is on line", row, Int(int64(line))))
		for i, col := range header {
			if i < len(rec) && rec[i] != "" {
				out = append(out, fact("has the cell", row, Str(col), readCell(rec[i])))
			}
		}
	}
	return out, nil
}

type certSpec struct {
	table, part, subject, value string
}

func certificateSpec(g *DB) (certSpec, bool) {
	for _, t := range g.ask(qRowFor) {
		if t.text("row") != rowPart {
			continue
		}
		spec := certSpec{table: t.text("table")}
		for _, c := range g.ask(qColumn) {
			if c.text("table") != spec.table {
				continue
			}
			switch c.text("value") {
			case colPart:
				spec.part = c.text("column")
			case colSubject:
				spec.subject = c.text("column")
			case colPartValue:
				spec.value = c.text("column")
			}
		}
		if spec.part != "" && spec.subject != "" && spec.value != "" {
			return spec, true
		}
	}
	return certSpec{}, false
}

func sqlName(s string) string { return `"` + strings.ReplaceAll(s, `"`, `""`) + `"` }

func (m *Machine) isProven(lv string, spec certSpec) bool {
	path := filepath.Join(m.root, lv+".db")
	if st, err := os.Stat(path); err != nil || !st.Mode().IsRegular() {
		return false
	}
	conn, err := sql.Open("sqlite", path)
	if err != nil {
		return false
	}
	defer conn.Close()
	rows, err := conn.Query(fmt.Sprintf("SELECT %s, %s, %s FROM %s", sqlName(spec.part), sqlName(spec.subject), sqlName(spec.value), sqlName(spec.table)))
	if err != nil {
		return false
	}
	defer rows.Close()
	answer, fresh := false, true
	for rows.Next() {
		var part, subject, value sql.NullString
		if err := rows.Scan(&part, &subject, &value); err != nil {
			return false
		}
		if part.String == partAnswer && value.String == "true" {
			answer = true
		}
		if subject.String != "" {
			p, ok := within(m.root, subject.String)
			if !ok {
				fresh = false
				continue
			}
			if h, err := hashFile(p); err != nil || h != value.String {
				fresh = false
			}
		}
	}
	return rows.Err() == nil && answer && fresh
}

func blanksOf(atoms []Atom) []string {
	var out []string
	seen := map[string]bool{}
	for _, a := range atoms {
		for _, t := range a.Args {
			if t.IsBlank() && !seen[t.Blank] {
				seen[t.Blank] = true
				out = append(out, t.Blank)
			}
		}
	}
	return out
}

func (r *Rule) atoms() []Atom {
	out := []Atom{r.Head}
	for _, c := range r.Conds {
		out = append(out, c.Atom)
	}
	return out
}

func patternPositions(rules []*Rule) map[string]map[int]bool {
	pos := map[string]map[int]bool{}
	mark := func(a Atom) bool {
		changed := false
		for i, t := range a.Args {
			if t.Blank != "fact pattern" {
				continue
			}
			if pos[a.Key()] == nil {
				pos[a.Key()] = map[int]bool{}
			}
			if !pos[a.Key()][i] {
				pos[a.Key()][i] = true
				changed = true
			}
		}
		return changed
	}
	var atoms []Atom
	for _, r := range rules {
		atoms = append(atoms, r.atoms()...)
	}
	for _, a := range atoms {
		mark(a)
	}
	for changed := true; changed; {
		changed = false
		for _, a := range atoms {
			for i, t := range a.Args {
				if t.isText() && pos[a.Key()][i] {
					if p, ok := parsePattern(t.Val.S); ok && mark(p) {
						changed = true
					}
				}
			}
		}
	}
	return pos
}

func (m *Machine) settle() error {
	g := groundDB(m.sourceRules())
	if spec, ok := certificateSpec(g); ok {
		for _, lv := range m.levels {
			if lv != m.level && m.isProven(lv, spec) {
				m.proven = append(m.proven, lv)
			}
		}
	}
	private := map[string]bool{}
	for _, b := range g.ask(qPrivate) {
		if a, ok := parsePattern(b.text("fact pattern")); ok {
			private[a.Key()] = true
		}
	}
	for _, s := range m.sources {
		for _, lv := range m.proven {
			if strings.HasPrefix(s.Name, lv+"/") {
				s.Certified = true
			}
		}
		for _, r := range s.Rules {
			if s.Certified && private[r.Head.Key()] {
				continue
			}
			m.rules = append(m.rules, r)
		}
	}
	m.builtins = map[string]*Builtin{}
	for _, b := range groundDB(m.rules).ask(qMangle) {
		line, text := b.text("line"), b.text("mangle")
		a, err := parseAtom(line)
		if err != nil || len(a.Args) == 0 || text == mangleAtom(a)+"." {
			continue
		}
		vars := map[string]int{}
		for i, t := range a.Args {
			if !t.IsBlank() {
				vars = nil
				break
			}
			if _, dup := vars[camel(t.Blank)]; dup {
				vars = nil
				break
			}
			vars[camel(t.Blank)] = i
		}
		if vars == nil {
			continue
		}
		bi, err := parseMangle(text, vars)
		if err != nil {
			m.problem(fmt.Sprintf("engine.go cannot read %s as the mangle of %s: %v", quoteText(text), quoteText(line), err))
			continue
		}
		if old := m.builtins[a.Key()]; old != nil && old.text != text {
			m.problem(fmt.Sprintf("%s has two meanings in mangle", quoteText(line)))
			continue
		}
		m.builtins[a.Key()] = bi
	}
	for _, r := range m.rules {
		if m.builtins[r.Head.Key()] != nil {
			return fmt.Errorf("%s: a rule cannot define %s, which means a mangle builtin", r.place(), r.Head.Pred)
		}
		p, err := m.compile(r)
		if err != nil {
			return err
		}
		m.plans = append(m.plans, p)
	}
	if err := m.stratify(); err != nil {
		return err
	}
	m.static = m.staticFacts()
	return nil
}

func (m *Machine) compile(r *Rule) (*plan, error) {
	p := &plan{rule: r, key: r.Head.Key()}
	ids := map[string]int{}
	slotOf := func(t Term) slot {
		if !t.IsBlank() {
			return slot{v: -1, c: t.Val}
		}
		id, ok := ids[t.Blank]
		if !ok {
			id = len(p.names)
			ids[t.Blank] = id
			p.names = append(p.names, t.Blank)
		}
		return slot{v: id}
	}
	for _, t := range r.Head.Args {
		p.head = append(p.head, slotOf(t))
	}
	for _, c := range r.Conds {
		l := lit{key: c.Atom.Key(), neg: c.Neg, builtin: m.builtins[c.Atom.Key()]}
		for _, t := range c.Atom.Args {
			l.args = append(l.args, slotOf(t))
		}
		p.conds = append(p.conds, l)
	}
	uses := make([]int, len(p.names))
	mark := func(ss []slot) {
		seen := map[int]bool{}
		for _, s := range ss {
			if s.v >= 0 && !seen[s.v] {
				seen[s.v] = true
				uses[s.v]++
			}
		}
	}
	mark(p.head)
	for _, l := range p.conds {
		mark(l.args)
	}
	bound := make([]bool, len(p.names))
	ready := func(l lit) bool {
		if l.builtin != nil {
			for _, v := range l.builtin.needs(l.args, l.neg) {
				if !bound[v] {
					return false
				}
			}
			return true
		}
		if !l.neg {
			return true
		}
		for _, s := range l.args {
			if s.v >= 0 && uses[s.v] > 1 && !bound[s.v] {
				return false
			}
		}
		return true
	}
	left := append([]lit(nil), p.conds...)
	for len(left) > 0 {
		pick := -1
		for i, l := range left {
			if ready(l) {
				pick = i
				break
			}
		}
		if pick < 0 {
			return nil, fmt.Errorf("%s: no order of its conditions knows every blank in time", r.place())
		}
		l := left[pick]
		left = append(left[:pick], left[pick+1:]...)
		p.body = append(p.body, l)
		if l.neg {
			continue
		}
		if l.builtin != nil {
			if o := l.builtin.output(l.args); o >= 0 {
				bound[o] = true
			}
			continue
		}
		for _, s := range l.args {
			if s.v >= 0 {
				bound[s.v] = true
			}
		}
	}
	for _, s := range p.head {
		if s.v >= 0 && !bound[s.v] {
			return nil, fmt.Errorf("%s: no condition gives a value to [%s]", r.place(), p.names[s.v])
		}
	}
	return p, nil
}

func (m *Machine) stratify() error {
	adj := map[string][]string{}
	var nodes []string
	seen := map[string]bool{}
	node := func(k string) {
		if !seen[k] {
			seen[k] = true
			nodes = append(nodes, k)
		}
	}
	for _, p := range m.plans {
		node(p.key)
		for _, l := range p.conds {
			if l.builtin == nil {
				node(l.key)
				adj[p.key] = append(adj[p.key], l.key)
			}
		}
	}
	index, low := map[string]int{}, map[string]int{}
	onStack := map[string]bool{}
	comp := map[string]int{}
	var stack []string
	count := 0
	ncomp := 0
	var strong func(v string)
	strong = func(v string) {
		index[v], low[v] = count, count
		count++
		stack = append(stack, v)
		onStack[v] = true
		for _, w := range adj[v] {
			if _, ok := index[w]; !ok {
				strong(w)
				if low[w] < low[v] {
					low[v] = low[w]
				}
			} else if onStack[w] && index[w] < low[v] {
				low[v] = index[w]
			}
		}
		if low[v] == index[v] {
			for {
				w := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[w] = false
				comp[w] = ncomp
				if w == v {
					break
				}
			}
			ncomp++
		}
	}
	for _, v := range nodes {
		if _, ok := index[v]; !ok {
			strong(v)
		}
	}
	m.strata = make([][]*plan, ncomp)
	m.loops = make([]bool, ncomp)
	for _, p := range m.plans {
		c := comp[p.key]
		m.strata[c] = append(m.strata[c], p)
		for _, l := range p.conds {
			if l.builtin != nil || comp[l.key] != c {
				continue
			}
			if l.neg {
				return fmt.Errorf("%s: %s depends on not %s, which depends on it", p.rule.place(), p.rule.Head.Pred, l.key)
			}
			m.loops[c] = true
		}
	}
	return nil
}

func (m *Machine) staticFacts() []Atom {
	var out []Atom
	positions := patternPositions(m.rules)
	var patterns []string
	seenPattern := map[string]bool{}
	for _, r := range m.rules {
		name := Str(r.Name)
		out = append(out,
			fact("is in the file", name, Str(r.File)),
			fact("is on line", name, Int(int64(r.Line))),
			fact("defines", name, Str(r.Head.Pred)),
			fact("has a rule for", Str(r.File), Str(r.Head.Pred)))
		for _, c := range r.Conds {
			out = append(out, fact("refers to", name, Str(c.Atom.Pred)))
		}
		if r.Head.Pred == "breaks" && len(r.Head.Args) == 2 && r.Head.Args[1].isText() {
			out = append(out, fact("lays down", name, r.Head.Args[1].Val))
		}
		for _, b := range blanksOf(r.atoms()) {
			out = append(out, fact("has the blank", name, Str(b)))
		}
		if strings.Join(r.render(), "\n") != r.text() {
			out = append(out, fact("read back differently", name))
		}
		for _, a := range r.atoms() {
			for i, t := range a.Args {
				if t.isText() && positions[a.Key()][i] && !seenPattern[t.Val.S] {
					seenPattern[t.Val.S] = true
					patterns = append(patterns, t.Val.S)
				}
			}
		}
	}
	for _, p := range patterns {
		a, ok := parsePattern(p)
		if !ok {
			m.problem(p + " is not a fact pattern")
			continue
		}
		out = append(out, fact("names", Str(p), Str(a.Pred)))
		for _, s := range blanksOf([]Atom{a}) {
			out = append(out, fact("has the slot", Str(p), Str(s)))
		}
	}
	for _, q := range engineQueries {
		a, _ := parseAtom(q)
		out = append(out, fact("refers to", Str(m.engineName), Str(a.Pred)))
	}
	for _, s := range m.sources {
		out = append(out, s.Rows...)
		if s.Read && s.Certified {
			out = append(out, fact("certified", Str(s.Name)))
		}
	}
	for _, lv := range m.proven {
		out = append(out, fact("proven", Str(lv)))
	}
	if m.change {
		out = append(out, fact("this run is a change"))
	}
	return out
}

func (m *Machine) evaluate(base []entry) *DB {
	db := newDB()
	for _, e := range base {
		db.addFact(e.a, e.origin)
	}
	for i, stratum := range m.strata {
		for {
			changed := false
			for _, p := range stratum {
				var out [][]Value
				env := make([]Value, len(p.names))
				bound := make([]bool, len(p.names))
				db.solve(p, 0, env, bound, func() { out = append(out, ground(p.head, env)) })
				for _, t := range out {
					if db.add(p.rule.Head.Pred, t) {
						changed = true
					}
				}
			}
			if !m.loops[i] || !changed {
				break
			}
		}
	}
	return db
}

func (m *Machine) base(returned, extra []entry) []entry {
	var out []entry
	for _, a := range m.static {
		out = append(out, entry{a, m.engineName})
	}
	m.mu.Lock()
	for _, p := range m.problems {
		out = append(out, entry{fact("a problem", Str(p)), m.engineName})
	}
	m.mu.Unlock()
	out = append(out, returned...)
	return append(out, extra...)
}

type call struct {
	command, tool, input Value
}

func (m *Machine) think() *DB {
	var returned, extra []entry
	ran := map[string]bool{}
	settled := false
	for {
		db := m.evaluate(m.base(returned, extra))
		var todo []call
		for _, b := range db.ask(qCalls) {
			c := call{b["command"], b["tool"], b["input"]}
			k := tupleKey([]Value{c.command, c.tool, c.input})
			if !ran[k] {
				ran[k] = true
				todo = append(todo, c)
			}
		}
		if len(todo) > 0 {
			returned = append(returned, m.runCalls(db, todo)...)
			continue
		}
		if !settled {
			settled = true
			extra = m.expectations(db)
			m.check(db)
			continue
		}
		return db
	}
}

func (m *Machine) expectations(db *DB) []entry {
	var out []entry
	look := func(query, pred string, want bool) {
		for _, b := range db.ask(query) {
			f := b["fact"]
			a, err := parseAtom(f.Text())
			if err != nil {
				m.problem(fmt.Sprintf("%s cannot be read as a fact: %v", quoteText(f.Text()), err))
			}
			if (err == nil && db.has(a)) == want {
				out = append(out, entry{fact(pred, f), m.engineName})
			}
		}
	}
	look(qExpects, "missing", false)
	look(qRulesOut, "present", true)
	return out
}

func (m *Machine) translate(line string) (string, error) {
	a, err := parseAtom(line)
	if err != nil {
		return "", err
	}
	if b := m.builtins[a.Key()]; b != nil {
		return b.render(a), nil
	}
	return mangleAtom(a) + ".", nil
}

func (m *Machine) check(db *DB) {
	for _, b := range db.ask(qMangle) {
		line, text := b.text("line"), b.text("mangle")
		got, err := m.translate(line)
		if err != nil {
			m.problem(fmt.Sprintf("engine.go cannot read %s as a line: %v", quoteText(line), err))
			continue
		}
		if got != text {
			m.problem(fmt.Sprintf("%s means in mangle %s but engine.go reads it as %s", quoteText(line), quoteText(text), quoteText(got)))
		}
	}
	for _, b := range db.ask(qComputed) {
		term, d := b.text("term"), b.text("description")
		if want, ok := computations[term]; !ok || want != d {
			m.problem(fmt.Sprintf("engine.go does not compute %s as %s", term, d))
		}
	}
	for _, b := range db.ask(qLoadedAs) {
		if !ways[b.text("way")] {
			m.problem(fmt.Sprintf("engine.go cannot load %s as %s", b.text("language"), b.text("way")))
		}
	}
	self := filepath.Base(m.engineName)
	for _, b := range db.ask(qPrints) {
		if b.text("go file") == self && b.text("knowledge") != theKnowledge {
			m.problem("engine.go prints only the knowledge, not " + b.text("knowledge"))
		}
	}
	for _, b := range db.ask(qPrintsIn) {
		if b.text("go file") == self && b.text("language") != plainLanguage {
			m.problem("engine.go prints only in plain language, not in " + b.text("language"))
		}
	}
	for _, b := range db.ask(qPrintsTo) {
		if b.text("go file") == self && b.text("output") != standardOutput {
			m.problem("engine.go prints only to standard output, not to " + b.text("output"))
		}
	}
	for _, b := range db.ask(qPublishedTo) {
		store := b.text("store")
		files := 0
		for _, f := range db.ask(qSqlite) {
			if f.text("store") != store {
				continue
			}
			files++
			if f.text("file") != theLevelStore {
				m.problem(fmt.Sprintf("engine.go publishes %s only to the level store, not to %s", store, f.text("file")))
			}
		}
		if files == 0 {
			m.problem(store + " is not a sqlite file")
		}
		for _, t := range db.ask(qTable) {
			if t.text("store") != store {
				continue
			}
			table := t.text("table")
			var kinds []string
			for _, r := range db.ask(qRowFor) {
				if r.text("table") == table {
					kinds = append(kinds, r.text("row"))
				}
			}
			if len(kinds) != 1 {
				m.problem(fmt.Sprintf("%s needs one kind of row, not %d", table, len(kinds)))
				continue
			}
			cols, ok := rowKinds[kinds[0]]
			if !ok {
				m.problem(fmt.Sprintf("engine.go cannot make a row for %s", kinds[0]))
				continue
			}
			for _, c := range db.ask(qColumn) {
				if c.text("table") != table {
					continue
				}
				known := false
				for _, d := range cols {
					known = known || d == c.text("value")
				}
				if !known || !c["number"].Num {
					m.problem(fmt.Sprintf("engine.go cannot fill the column %s of %s with %s", c.text("column"), table, c.text("value")))
				}
			}
		}
	}
	for _, b := range db.ask(qHolds) {
		if !certificateParts[b.text("part")] {
			m.problem("engine.go cannot put " + b.text("part") + " in the certificate")
		}
	}
	for _, q := range []string{qShows, qReasons} {
		for _, b := range db.ask(q) {
			if _, ok := parsePattern(b.text("fact pattern")); !ok {
				m.problem(b.text("fact pattern") + " is not a fact pattern")
			}
		}
	}
}

type derivation struct {
	fact    Atom
	line    string
	rule    *Rule
	reasons []string
	id      string
}

func (m *Machine) derive(db *DB) []derivation {
	var out []derivation
	seen := map[string]bool{}
	for _, p := range m.plans {
		env := make([]Value, len(p.names))
		bound := make([]bool, len(p.names))
		db.solve(p, 0, env, bound, func() {
			f := fact(p.rule.Head.Pred, ground(p.head, env)...)
			d := derivation{fact: f, line: renderAtom(f, false), rule: p.rule}
			for i, c := range p.conds {
				a := Atom{Pred: p.rule.Conds[i].Atom.Pred, Args: make([]Term, len(c.args))}
				for j, s := range c.args {
					switch {
					case s.v < 0:
						a.Args[j] = Term{Val: s.c}
					case bound[s.v]:
						a.Args[j] = Term{Val: env[s.v]}
					default:
						a.Args[j] = Term{Blank: p.names[s.v]}
					}
				}
				d.reasons = append(d.reasons, renderCondition(a, c.neg))
			}
			d.id = shortHash(strings.Join(append([]string{d.line, p.rule.Name}, d.reasons...), "\n"))
			if !seen[d.id] {
				seen[d.id] = true
				out = append(out, d)
			}
		})
	}
	return out
}

func matches(p, f Atom) bool {
	if p.Key() != f.Key() {
		return false
	}
	b := map[string]Value{}
	for i, t := range p.Args {
		v := f.Args[i].Val
		if !t.IsBlank() {
			if t.Val != v {
				return false
			}
			continue
		}
		if old, ok := b[t.Blank]; ok && old != v {
			return false
		}
		b[t.Blank] = v
	}
	return true
}

func (m *Machine) giveReasons(db *DB, ds []derivation) {
	for _, b := range db.ask(qReasons) {
		pat, ok := parsePattern(b.text("fact pattern"))
		if !ok {
			continue
		}
		for _, d := range ds {
			if !matches(pat, d.fact) {
				continue
			}
			for _, r := range d.reasons {
				db.addFact(fact("holds because", Str(d.line), Str(r)), m.engineName)
			}
		}
	}
}

func (db *DB) facts(key string) []Atom {
	r := db.rels[key]
	if r == nil {
		return nil
	}
	out := make([]Atom, len(r.tuples))
	for i, t := range r.tuples {
		out[i] = fact(db.preds[key], t...)
	}
	return out
}

func (m *Machine) print(db *DB) {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	answer, _ := parseAtom(qAnswer)
	printed := map[string]bool{}
	var last []string
	first := true
	for _, b := range db.ask(qShows) {
		pat, ok := parsePattern(b.text("fact pattern"))
		if !ok {
			continue
		}
		var lines []string
		for _, f := range db.facts(pat.Key()) {
			if !matches(pat, f) {
				continue
			}
			l := renderAtom(f, false)
			if !printed[l] {
				printed[l] = true
				lines = append(lines, l)
			}
		}
		sort.Strings(lines)
		if pat.Key() == answer.Key() {
			last = append(last, lines...)
			continue
		}
		if len(lines) == 0 {
			continue
		}
		if !first {
			fmt.Fprintln(w)
		}
		first = false
		for _, l := range lines {
			fmt.Fprintln(w, l)
		}
	}
	if len(last) > 0 {
		if !first {
			fmt.Fprintln(w)
		}
		for _, l := range last {
			fmt.Fprintln(w, l)
		}
	}
}

func (m *Machine) answer(db *DB) (string, int, bool) {
	answers := db.ask(qAnswer)
	if len(answers) != 1 {
		return "", 2, false
	}
	a := answers[0]["answer"]
	for _, b := range db.ask(qExit) {
		if b["answer"] == a && b["code"].Num {
			return a.Text(), int(b["code"].N), true
		}
	}
	return a.Text(), 2, false
}

type record map[string]Value

type column struct {
	n    int64
	name string
	desc string
}

type table struct {
	name string
	kind string
	cols []column
	rows []record
}

func (m *Machine) machineFiles(db *DB) []*Source {
	loadable := map[string]bool{}
	for _, b := range db.ask(qLoadedAs) {
		loadable[b.text("language")] = true
	}
	entries, err := os.ReadDir(m.machineDir)
	if err != nil {
		return nil
	}
	var out []*Source
	for _, e := range entries {
		if !e.Type().IsRegular() {
			continue
		}
		name := filepath.Base(m.machineDir) + "/" + e.Name()
		best, language := "", ""
		for _, b := range db.ask(qMeans) {
			end := b.text("ending")
			if end != "" && strings.HasSuffix(name, end) && len(end) > len(best) {
				best, language = end, b.text("language")
			}
		}
		if best != "" && !loadable[language] {
			out = append(out, &Source{Name: name, Path: filepath.Join(m.machineDir, e.Name())})
		}
	}
	return out
}

func (m *Machine) records(kind string, db *DB, ds []derivation, answer string) ([]record, error) {
	var out []record
	switch kind {
	case rowRule:
		in := map[string]bool{}
		for _, b := range db.ask(qInKnowledge) {
			in[b.text("rule")] = true
		}
		for _, r := range m.rules {
			if in[r.Name] {
				out = append(out, record{colRuleID: Str(r.Name), colRuleFile: Str(r.File), colRuleLine: Int(int64(r.Line)), colRuleText: Str(r.text())})
			}
		}
	case rowFact:
		for _, k := range db.keys {
			for _, t := range db.rels[k].tuples {
				line := renderAtom(fact(db.preds[k], t...), false)
				out = append(out, record{colFactID: Str(shortHash(line)), colFactText: Str(line), colOrigin: Str(db.originOf(k, t))})
			}
		}
		sort.Slice(out, func(i, j int) bool { return out[i][colFactText].S < out[j][colFactText].S })
	case rowDerive:
		for _, d := range ds {
			out = append(out, record{colDeriveID: Str(d.id), colFactID: Str(shortHash(d.line)), colRuleID: Str(d.rule.Name)})
		}
	case rowReason:
		for _, d := range ds {
			for i, r := range d.reasons {
				out = append(out, record{colDeriveID: Str(d.id), colReasonAt: Int(int64(i + 1)), colReason: Str(r)})
			}
		}
	case rowPart:
		for _, b := range db.ask(qHolds) {
			part := b.text("part")
			add := func(subject, value string) {
				out = append(out, record{colPart: Str(part), colSubject: Str(subject), colPartValue: Str(value)})
			}
			hashAll := func(sources []*Source) error {
				for _, s := range sources {
					if !s.Read {
						continue
					}
					h, err := hashFile(s.Path)
					if err != nil {
						return err
					}
					add(s.Name, h)
				}
				return nil
			}
			switch part {
			case partLevel:
				add("", m.level)
			case partLoaded:
				if err := hashAll(m.sources); err != nil {
					return nil, err
				}
			case partMachine:
				files := m.machineFiles(db)
				for _, f := range files {
					f.Read = true
				}
				if err := hashAll(files); err != nil {
					return nil, err
				}
			case partAnswer:
				add("", answer)
			}
		}
	}
	return out, nil
}

func (m *Machine) publish(db *DB, ds []derivation, answer string) error {
	for _, b := range db.ask(qPublishedTo) {
		store := b.text("store")
		when := false
		for _, w := range db.ask(qPublishedWhen) {
			when = when || w.text("answer") == answer
		}
		if !when {
			continue
		}
		path := ""
		for _, f := range db.ask(qSqlite) {
			if f.text("store") == store && f.text("file") == theLevelStore {
				path = filepath.Join(m.root, m.level+".db")
			}
		}
		if path == "" {
			continue
		}
		var tables []*table
		for _, t := range db.ask(qTable) {
			if t.text("store") != store {
				continue
			}
			tb := &table{name: t.text("table")}
			for _, r := range db.ask(qRowFor) {
				if r.text("table") == tb.name {
					tb.kind = r.text("row")
				}
			}
			for _, c := range db.ask(qColumn) {
				if c.text("table") == tb.name && c["number"].Num {
					tb.cols = append(tb.cols, column{c["number"].N, c.text("column"), c.text("value")})
				}
			}
			sort.Slice(tb.cols, func(i, j int) bool { return tb.cols[i].n < tb.cols[j].n })
			rows, err := m.records(tb.kind, db, ds, answer)
			if err != nil {
				return err
			}
			tb.rows = rows
			tables = append(tables, tb)
		}
		if err := writeStore(path, tables); err != nil {
			return err
		}
	}
	return nil
}

func writeStore(path string, tables []*table) error {
	tmp := path + ".new"
	os.Remove(tmp)
	conn, err := sql.Open("sqlite", tmp)
	if err != nil {
		return err
	}
	fail := func(err error) error {
		conn.Close()
		os.Remove(tmp)
		return err
	}
	tx, err := conn.Begin()
	if err != nil {
		return fail(err)
	}
	for _, t := range tables {
		names := make([]string, len(t.cols))
		marks := make([]string, len(t.cols))
		for i, c := range t.cols {
			names[i] = sqlName(c.name)
			marks[i] = "?"
		}
		if _, err := tx.Exec(fmt.Sprintf("CREATE TABLE %s (%s)", sqlName(t.name), strings.Join(names, ", "))); err != nil {
			tx.Rollback()
			return fail(err)
		}
		stmt, err := tx.Prepare(fmt.Sprintf("INSERT INTO %s VALUES (%s)", sqlName(t.name), strings.Join(marks, ", ")))
		if err != nil {
			tx.Rollback()
			return fail(err)
		}
		for _, r := range t.rows {
			args := make([]any, len(t.cols))
			for i, c := range t.cols {
				v, ok := r[c.desc]
				switch {
				case !ok:
					args[i] = nil
				case v.Num:
					args[i] = v.N
				default:
					args[i] = v.S
				}
			}
			if _, err := stmt.Exec(args...); err != nil {
				stmt.Close()
				tx.Rollback()
				return fail(err)
			}
		}
		stmt.Close()
	}
	if err := tx.Commit(); err != nil {
		return fail(err)
	}
	if err := conn.Close(); err != nil {
		os.Remove(tmp)
		return err
	}
	return os.Rename(tmp, path)
}

func main() {
	os.Exit(run())
}

func run() int {
	args := os.Args[1:]
	m := &Machine{seenProblem: map[string]bool{}}
	if len(args) > 0 && args[0] == "-change" {
		m.change = true
		args = args[1:]
	}
	if len(args) != 1 {
		fmt.Fprintln(os.Stderr, "engine.go needs the folder of the machine")
		return 2
	}
	steps := []func() error{func() error { return m.setup(args[0]) }, m.loadLevels, m.loadFiles, m.settle}
	for _, step := range steps {
		if err := step(); err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
	}
	db := m.think()
	ds := m.derive(db)
	m.giveReasons(db, ds)
	m.print(db)
	answer, code, ok := m.answer(db)
	if !ok {
		fmt.Fprintln(os.Stderr, "the knowledge gives no single answer with an exit code")
		return 2
	}
	if !m.change {
		if err := m.publish(db, ds, answer); err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 2
		}
	}
	return code
}
