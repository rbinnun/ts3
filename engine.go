package main

import (
	"crypto/sha256"
	"database/sql"
	"encoding/hex"
	"fmt"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/google/mangle/analysis"
	"github.com/google/mangle/ast"
	"github.com/google/mangle/engine"
	"github.com/google/mangle/factstore"
	"github.com/google/mangle/parse"
	_ "modernc.org/sqlite"
)

const (
	self         = "engine.go"
	firstFile    = "spec.plain"
	brokenAnswer = "broken"
	plainLoader  = "rules and facts"
	rowsLoader   = "a row per line with a cell per column"
	auxPrefix    = "derivation__"
)

var computations = map[string]string{
	"a rule id":       "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":       "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a derivation id": "the first 16 hex digits of the sha256 of the fact and the rule name and the reasons as plain lines joined by newlines",
	"a row name":      "the file name and a colon and the line number",
	"a cell value":    "the cell text read as a plain value",
}

var (
	intForm   = regexp.MustCompile(`^(0|-?[1-9][0-9]*)$`)
	blankForm = regexp.MustCompile(`^\[([^\[\]]+)\]$`)
	blankAny  = regexp.MustCompile(`\[[^\[\]]+\]`)
	propForm  = regexp.MustCompile(`^[A-Za-z0-9]+( [A-Za-z0-9]+)*$`)
	identForm = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)
)

type val struct {
	isNum bool
	n     int64
	s     string
}

func text(s string) val { return val{s: s} }

func number(n int64) val { return val{isNum: true, n: n} }

func plainValue(s string) val {
	if intForm.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return number(n)
		}
	}
	return text(s)
}

func (v val) String() string {
	if v.isNum {
		return strconv.FormatInt(v.n, 10)
	}
	return v.s
}

func (v val) key() string {
	if v.isNum {
		return "n" + strconv.FormatInt(v.n, 10)
	}
	return "s" + v.s
}

func (v val) sqlValue() any {
	if v.isNum {
		return v.n
	}
	return v.s
}

func (v val) mangle() string {
	if v.isNum {
		return strconv.FormatInt(v.n, 10)
	}
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range v.s {
		switch {
		case r == '\\':
			b.WriteString(`\\`)
		case r == '"':
			b.WriteString(`\"`)
		case r == '\n':
			b.WriteString(`\n`)
		case r == '\t':
			b.WriteString(`\t`)
		case r < 0x20:
			fmt.Fprintf(&b, `\x%02x`, r)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func fromConstant(c ast.Constant) val {
	switch c.Type {
	case ast.NumberType:
		return number(c.NumValue)
	case ast.StringType:
		return text(c.Symbol)
	}
	return text(c.String())
}

func rowKey(args []val) string {
	parts := make([]string, len(args))
	for i, a := range args {
		parts[i] = a.key()
	}
	return strings.Join(parts, "\x00")
}

func hash16(s string) string {
	return hashHex([]byte(s))[:16]
}

func hashHex(b []byte) string {
	h := sha256.Sum256(b)
	return hex.EncodeToString(h[:])
}

func oneLine(s string) string {
	return strings.Join(strings.Fields(s), " ")
}

type term struct {
	blank string
	v     val
}

type stmt struct {
	neg  bool
	prop string
	subj term
	verb string
	objs []term
}

const (
	propKind = iota
	isKind
	verbKind
)

type shape struct {
	kind   int
	phrase string
	arity  int
}

func words(s string) []string {
	return strings.FieldsFunc(s, func(r rune) bool {
		return !(r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9')
	})
}

func snake(s string) string {
	n := strings.ToLower(strings.Join(words(s), "_"))
	if n == "" || n[0] < 'a' || n[0] > 'z' {
		n = "p_" + n
	}
	switch n {
	case "bound", "let", "do", "descr", "inclusion", "opt":
		n += "_"
	}
	return n
}

func varName(blank string) string {
	var b strings.Builder
	for _, w := range words(blank) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	n := b.String()
	if n == "" || n[0] < 'A' || n[0] > 'Z' {
		n = "V" + n
	}
	switch n {
	case "Package", "Use", "Decl":
		n += "V"
	}
	return n
}

func baseSlot(blank string) string {
	for _, p := range []string{"any ", "other "} {
		if strings.HasPrefix(blank, p) {
			return blank[len(p):]
		}
	}
	return blank
}

func (sh shape) name() string { return snake(sh.phrase) }

func (sh shape) stmt(args []val) stmt {
	switch sh.kind {
	case propKind:
		return stmt{prop: sh.phrase}
	case isKind:
		return stmt{subj: term{v: args[0]}, verb: "is", objs: []term{{v: text(sh.phrase)}}}
	}
	st := stmt{subj: term{v: args[0]}, verb: sh.phrase}
	for _, a := range args[1:] {
		st.objs = append(st.objs, term{v: a})
	}
	return st
}

func (st stmt) shape() shape {
	if st.prop != "" {
		return shape{propKind, st.prop, 0}
	}
	if st.verb == "is" && len(st.objs) == 1 && st.objs[0].blank == "" && !st.objs[0].v.isNum && !needsQuotes(st.objs[0].v.s) {
		return shape{isKind, st.objs[0].v.s, 1}
	}
	return shape{verbKind, st.verb, 1 + len(st.objs)}
}

func (st stmt) args() []term {
	switch st.shape().kind {
	case propKind:
		return nil
	case isKind:
		return []term{st.subj}
	}
	return append([]term{st.subj}, st.objs...)
}

func (st stmt) terms() []term {
	if st.prop != "" {
		return nil
	}
	return append([]term{st.subj}, st.objs...)
}

func (st stmt) blanks() []string {
	var out []string
	for _, t := range st.terms() {
		if t.blank != "" {
			out = append(out, t.blank)
		}
	}
	return out
}

func (st stmt) fill(bind map[string]val) stmt {
	fillTerm := func(t term) term {
		if t.blank != "" {
			if v, ok := bind[varName(t.blank)]; ok {
				return term{v: v}
			}
		}
		return t
	}
	out := stmt{neg: st.neg, prop: st.prop, verb: st.verb}
	if st.prop == "" {
		out.subj = fillTerm(st.subj)
		for _, o := range st.objs {
			out.objs = append(out.objs, fillTerm(o))
		}
	}
	return out
}

func needsQuotes(s string) bool {
	return s == "" || strings.Contains(s, ", ") || s != strings.TrimSpace(s) ||
		s[0] == '"' || s[0] == '\'' || blankForm.MatchString(s) || intForm.MatchString(s) ||
		strings.ContainsAny(s, "\n\r")
}

func quoteValue(s string) string {
	if !needsQuotes(s) {
		return s
	}
	for _, q := range []string{`"`, `'`} {
		if !strings.Contains(s, q+", ") && !strings.HasSuffix(s, q) {
			return q + s + q
		}
	}
	return `"` + s + `"`
}

func renderTerm(t term) string {
	if t.blank != "" {
		return "[" + t.blank + "]"
	}
	if t.v.isNum {
		return t.v.String()
	}
	return quoteValue(t.v.s)
}

func (st stmt) render() string {
	out := st.prop
	if st.prop == "" {
		parts := []string{renderTerm(st.subj), st.verb}
		for _, o := range st.objs {
			parts = append(parts, renderTerm(o))
		}
		out = strings.Join(parts, ", ")
	}
	if st.neg {
		return "not " + out
	}
	return out
}

func splitParts(s string) ([]string, []bool, bool) {
	var parts []string
	var quoted []bool
	i := 0
	for {
		if i < len(s) && (s[i] == '"' || s[i] == '\'') {
			q := s[i]
			end := -1
			for j := i + 1; j < len(s); j++ {
				if s[j] == q && (j+1 == len(s) || strings.HasPrefix(s[j+1:], ", ")) {
					end = j
					break
				}
			}
			if end < 0 {
				return nil, nil, false
			}
			parts = append(parts, s[i+1:end])
			quoted = append(quoted, true)
			i = end + 1
		} else {
			k := strings.Index(s[i:], ", ")
			if k < 0 {
				return append(parts, s[i:]), append(quoted, false), true
			}
			parts = append(parts, s[i:i+k])
			quoted = append(quoted, false)
			i += k
		}
		if i >= len(s) {
			return parts, quoted, true
		}
		i += 2
	}
}

func readTerm(raw string, quoted bool) (term, bool) {
	if quoted {
		return term{v: text(raw)}, true
	}
	if raw == "" {
		return term{}, false
	}
	if m := blankForm.FindStringSubmatch(raw); m != nil {
		return term{blank: m[1]}, true
	}
	return term{v: plainValue(raw)}, true
}

func readStmt(s string) (stmt, bool) {
	if s != "" && !strings.Contains(s, ", ") && s[0] != '"' && s[0] != '\'' {
		if propForm.MatchString(s) {
			return stmt{prop: s}, true
		}
		return stmt{}, false
	}
	raws, quoted, ok := splitParts(s)
	if !ok || len(raws) < 3 || quoted[1] || raws[1] == "" || blankForm.MatchString(raws[1]) {
		return stmt{}, false
	}
	subj, ok := readTerm(raws[0], quoted[0])
	if !ok {
		return stmt{}, false
	}
	st := stmt{subj: subj, verb: raws[1]}
	for i := 2; i < len(raws); i++ {
		t, ok := readTerm(raws[i], quoted[i])
		if !ok {
			return stmt{}, false
		}
		st.objs = append(st.objs, t)
	}
	return st, true
}

func readPattern(p string) (shape, []string, bool) {
	locs := blankAny.FindAllStringIndex(p, -1)
	if len(locs) == 0 {
		if propForm.MatchString(p) {
			return shape{propKind, p, 0}, nil, true
		}
		return shape{}, nil, false
	}
	if locs[0][0] != 0 {
		return shape{}, nil, false
	}
	var slots []string
	for _, l := range locs {
		slots = append(slots, p[l[0]+1:l[1]-1])
	}
	if len(locs) == 1 {
		rest := p[locs[0][1]:]
		if len(rest) < 2 || rest[0] != ' ' || strings.TrimSpace(rest) != rest[1:] {
			return shape{}, nil, false
		}
		phrase := rest[1:]
		if strings.HasPrefix(phrase, "is ") && !needsQuotes(phrase[3:]) {
			return shape{isKind, phrase[3:], 1}, slots, true
		}
		return shape{verbKind, phrase, 1}, slots, true
	}
	mid := p[locs[0][1]:locs[1][0]]
	if len(mid) < 3 || mid[0] != ' ' || mid[len(mid)-1] != ' ' || strings.TrimSpace(mid) != mid[1:len(mid)-1] {
		return shape{}, nil, false
	}
	for i := 1; i+1 < len(locs); i++ {
		if p[locs[i][1]:locs[i+1][0]] != " " {
			return shape{}, nil, false
		}
	}
	if locs[len(locs)-1][1] != len(p) {
		return shape{}, nil, false
	}
	return shape{verbKind, mid[1 : len(mid)-1], len(locs)}, slots, true
}

type piece struct {
	lit string
	arg int
}

type template struct {
	arity  int
	pieces []piece
}

func (t template) fill(args []string) string {
	var b strings.Builder
	for _, p := range t.pieces {
		if p.arg < 0 {
			b.WriteString(p.lit)
		} else {
			b.WriteString(args[p.arg])
		}
	}
	return b.String()
}

func (t template) same(o template) bool {
	return t.arity == o.arity && fmt.Sprint(t.pieces) == fmt.Sprint(o.pieces)
}

type rule struct {
	file   string
	line   int
	lines  []string
	joins  []string
	head   stmt
	conds  []stmt
	clause string
	aux    string
	vars   []string
	broken bool
}

func (r *rule) name() string { return fmt.Sprintf("%s:%d", r.file, r.line) }

func (r *rule) text() string { return strings.Join(r.lines, "\n") }

func (r *rule) rendered() string {
	out := []string{r.head.render()}
	for i, c := range r.conds {
		join := "and"
		if i == 0 {
			join = "if"
		}
		out = append(out, "    "+join+" "+c.render())
	}
	return strings.Join(out, "\n")
}

type fact struct {
	pred string
	args []val
	by   string
}

type derivation struct {
	id      string
	fact    string
	factID  string
	pred    string
	rule    string
	reasons []string
}

type machine struct {
	change      string
	rules       []*rule
	facts       []fact
	post        []fact
	seen        map[string]bool
	shapes      map[string]shape
	builtins    map[string]template
	patterns    map[string]string
	problems    []string
	problemSeen map[string]bool
	loaded      []string
	hashes      map[string]string
	known       map[string][][]val
	derivations []derivation
	mu          sync.Mutex
}

func newMachine() *machine {
	return &machine{
		seen:        map[string]bool{},
		shapes:      map[string]shape{},
		builtins:    map[string]template{},
		patterns:    map[string]string{},
		problemSeen: map[string]bool{},
		hashes:      map[string]string{},
	}
}

func (m *machine) problem(format string, args ...any) {
	p := oneLine(fmt.Sprintf(format, args...))
	if !m.problemSeen[p] {
		m.problemSeen[p] = true
		m.problems = append(m.problems, p)
	}
}

func (m *machine) register(sh shape) string {
	n := sh.name()
	if old, ok := m.shapes[n]; ok && old != sh {
		m.problem("%s is written both as %q and as %q", n, old.phrase, sh.phrase)
		return n
	}
	m.shapes[n] = sh
	return n
}

func (m *machine) predOf(pattern string) string {
	m.mu.Lock()
	defer m.mu.Unlock()
	if p, ok := m.patterns[pattern]; ok {
		return p
	}
	sh, _, ok := readPattern(pattern)
	if !ok {
		m.problem("%s cannot read the pattern %s", self, pattern)
		m.patterns[pattern] = ""
		return ""
	}
	p := m.register(sh)
	m.patterns[pattern] = p
	return p
}

func (m *machine) emit(by, pattern string, args ...val) {
	pred := m.predOf(pattern)
	if pred == "" {
		return
	}
	k := pred + "\x01" + rowKey(args)
	if m.seen[k] {
		return
	}
	m.seen[k] = true
	m.facts = append(m.facts, fact{pred, args, by})
}

func (m *machine) line(pred string, args []val) string {
	if sh, ok := m.shapes[pred]; ok && sh.arity == len(args) {
		return sh.stmt(args).render()
	}
	parts := []string{pred}
	for _, a := range args {
		parts = append(parts, quoteValue(a.String()))
	}
	return strings.Join(parts, ", ")
}

func (m *machine) stated(pred string) [][]val {
	var out [][]val
	for _, r := range m.rules {
		if r.broken || len(r.conds) > 0 || len(r.head.blanks()) > 0 || r.head.shape().name() != pred {
			continue
		}
		var args []val
		for _, t := range r.head.args() {
			args = append(args, t.v)
		}
		out = append(out, args)
	}
	return out
}

func (m *machine) factsOf(pred string) [][]val {
	if m.known == nil {
		return m.stated(pred)
	}
	out := append([][]val{}, m.known[pred]...)
	for _, f := range m.post {
		if f.pred == pred {
			out = append(out, f.args)
		}
	}
	return out
}

func (m *machine) ordered(pred string) [][]val {
	var out [][]val
	have := map[string]bool{}
	for _, a := range m.stated(pred) {
		if !have[rowKey(a)] {
			have[rowKey(a)] = true
			out = append(out, a)
		}
	}
	if m.known != nil {
		for _, a := range m.factsOf(pred) {
			if !have[rowKey(a)] {
				have[rowKey(a)] = true
				out = append(out, a)
			}
		}
	}
	return out
}

func (m *machine) objectsOf(pattern string, subject string) []val {
	var out []val
	for _, a := range m.ordered(m.predOf(pattern)) {
		if len(a) == 2 && a[0].String() == subject {
			out = append(out, a[1])
		}
	}
	return out
}

func (m *machine) load() {
	loaders := map[string]func(string, string){plainLoader: m.loadPlain, rowsLoader: m.loadRows}
	queue := []string{firstFile}
	done := map[string]bool{}
	for len(queue) > 0 {
		f := queue[0]
		queue = queue[1:]
		if done[f] {
			continue
		}
		done[f] = true
		data, err := os.ReadFile(f)
		if err != nil {
			if f == firstFile {
				m.problem("%s cannot read %s", self, f)
			}
			continue
		}
		kind := plainLoader
		if f != firstFile {
			kind = m.loaderFor(f)
		}
		load, ok := loaders[kind]
		if !ok {
			m.problem("%s does not know how to load %s", self, f)
			continue
		}
		m.loaded = append(m.loaded, f)
		m.hashes[f] = hashHex(data)
		load(f, string(data))
		for _, next := range m.objectsOf("[go file] loads [file]", self) {
			if !done[next.String()] {
				queue = append(queue, next.String())
			}
		}
	}
	for _, a := range m.ordered(m.predOf("[language] is loaded as [kind]")) {
		if _, ok := loaders[a[1].String()]; !ok {
			m.problem("%s cannot load %s as %s", self, a[0], a[1])
		}
	}
}

func (m *machine) loaderFor(f string) string {
	language, best := "", -1
	for _, a := range m.ordered(m.predOf("[ending] means [language]")) {
		e := a[0].String()
		if strings.HasSuffix(f, e) && len(e) > best {
			language, best = a[1].String(), len(e)
		}
	}
	if best < 0 {
		return ""
	}
	kinds := m.objectsOf("[language] is loaded as [kind]", language)
	if len(kinds) != 1 {
		return ""
	}
	return kinds[0].String()
}

func (m *machine) loadPlain(file, data string) {
	lines := strings.Split(data, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var cur *rule
	for i, ln := range lines {
		at := fmt.Sprintf("%s:%d", file, i+1)
		if strings.TrimSpace(ln) == "" {
			cur = nil
			continue
		}
		if ln[0] == ' ' || ln[0] == '\t' {
			join, rest := "", ""
			switch {
			case strings.HasPrefix(ln, "    if "):
				join, rest = "if", ln[len("    if "):]
			case strings.HasPrefix(ln, "    and "):
				join, rest = "and", ln[len("    and "):]
			default:
				m.problem("%s cannot be read: %s", at, ln)
				continue
			}
			if cur == nil {
				m.problem("%s is a condition without a rule: %s", at, ln)
				continue
			}
			neg := strings.HasPrefix(rest, "not ")
			if neg {
				rest = rest[len("not "):]
			}
			st, ok := readStmt(rest)
			if !ok {
				m.problem("%s cannot be read: %s", at, ln)
				cur.broken = true
				continue
			}
			st.neg = neg
			cur.conds = append(cur.conds, st)
			cur.joins = append(cur.joins, join)
			cur.lines = append(cur.lines, ln)
			continue
		}
		st, ok := readStmt(ln)
		if !ok {
			m.problem("%s cannot be read: %s", at, ln)
			cur = nil
			continue
		}
		cur = &rule{file: file, line: i + 1, lines: []string{ln}, head: st}
		m.rules = append(m.rules, cur)
	}
}

func (m *machine) loadRows(file, data string) {
	lines := strings.Split(data, "\n")
	if len(lines) == 0 {
		return
	}
	header := strings.Split(strings.TrimSuffix(lines[0], "\r"), ",")
	for i := 1; i < len(lines); i++ {
		ln := strings.TrimSuffix(lines[i], "\r")
		if ln == "" {
			continue
		}
		cells := strings.Split(ln, ",")
		if len(cells) != len(header) {
			m.problem("%s:%d does not have one cell for each column", file, i+1)
			continue
		}
		row := text(fmt.Sprintf("%s:%d", file, i+1))
		m.emit(self, "[row] is a row of [source]", row, text(file))
		m.emit(self, "[row] is on line [number]", row, number(int64(i+1)))
		for j, c := range cells {
			m.emit(self, "[row] has the cell [column] [value]", row, text(header[j]), plainValue(c))
		}
	}
}

func (m *machine) isBuiltin(st stmt) bool {
	if st.prop != "" {
		return false
	}
	_, ok := m.builtins[st.verb]
	return ok
}

func (m *machine) atomText(st stmt) string {
	if st.prop == "" {
		if t, ok := m.builtins[st.verb]; ok {
			var args []string
			for _, a := range st.terms() {
				args = append(args, mangleTerm(a))
			}
			if t.arity != len(args) {
				m.problem("%s needs %d parts but has %d: %s", st.verb, t.arity, len(args), st.render())
				return ""
			}
			return t.fill(args)
		}
	}
	name := m.register(st.shape())
	var args []string
	for _, a := range st.args() {
		args = append(args, mangleTerm(a))
	}
	return name + "(" + strings.Join(args, ", ") + ")"
}

func mangleTerm(t term) string {
	if t.blank != "" {
		return varName(t.blank)
	}
	return t.v.mangle()
}

func (m *machine) learnMangle() {
	type example struct {
		st   stmt
		want string
		line string
	}
	var examples []example
	for _, a := range m.ordered(m.predOf("[line] means in mangle [mangle]")) {
		st, ok := readStmt(a[0].String())
		if !ok {
			m.problem("%s cannot read %s", self, a[0])
			continue
		}
		examples = append(examples, example{st, a[1].String(), a[0].String()})
	}
	for _, e := range examples {
		if strings.HasSuffix(e.want, ".") || e.st.prop != "" {
			continue
		}
		index := map[string]int{}
		all := true
		for i, t := range e.st.terms() {
			if t.blank == "" {
				all = false
				break
			}
			index[varName(t.blank)] = i
		}
		if !all || len(index) != len(e.st.terms()) {
			continue
		}
		t := template{arity: len(e.st.terms())}
		last := 0
		for _, loc := range identForm.FindAllStringIndex(e.want, -1) {
			if i, ok := index[e.want[loc[0]:loc[1]]]; ok {
				t.pieces = append(t.pieces, piece{e.want[last:loc[0]], -1}, piece{"", i})
				last = loc[1]
			}
		}
		t.pieces = append(t.pieces, piece{e.want[last:], -1})
		if old, ok := m.builtins[e.st.verb]; ok && !old.same(t) {
			m.problem("%s means two different things in mangle", e.st.verb)
			continue
		}
		m.builtins[e.st.verb] = t
	}
	for _, e := range examples {
		got := m.atomText(e.st)
		if !m.isBuiltin(e.st) {
			got += "."
		}
		if got != e.want {
			m.problem("%s reads %s as %s and not as %s", self, e.line, got, e.want)
		}
	}
}

func (m *machine) translate() {
	for i, r := range m.rules {
		if r.broken {
			continue
		}
		if m.isBuiltin(r.head) {
			m.problem("%s defines %s, which is built in", r.name(), r.head.verb)
			r.broken = true
			continue
		}
		head := m.atomText(r.head)
		if len(r.conds) == 0 {
			r.clause = head + "."
			continue
		}
		var body []string
		have := map[string]bool{}
		for _, c := range r.conds {
			a := m.atomText(c)
			if c.neg {
				if m.isBuiltin(c) {
					m.problem("%s denies %s, which is built in", r.name(), c.verb)
					r.broken = true
				}
				a = "!" + a
			} else {
				for _, b := range c.blanks() {
					if v := varName(b); !have[v] {
						have[v] = true
						r.vars = append(r.vars, v)
					}
				}
			}
			body = append(body, a)
		}
		r.clause = head + " :- " + strings.Join(body, ", ") + "."
		r.aux = fmt.Sprintf("%s%d(%s) :- %s.", auxPrefix, i, strings.Join(r.vars, ", "), strings.Join(body, ", "))
	}
}

func (m *machine) describe() {
	for _, a := range m.ordered(m.predOf("[kind] is computed as [method]")) {
		if computations[a[0].String()] != a[1].String() {
			m.problem("%s cannot compute %s as %s", self, a[0], a[1])
		}
	}
	labels := map[string]bool{}
	label := func(pred string, i int) bool {
		k := fmt.Sprintf("%s/%d", pred, i)
		if labels[k] {
			return false
		}
		labels[k] = true
		return true
	}
	var stmts []stmt
	for _, r := range m.rules {
		if r.broken {
			continue
		}
		for _, st := range append([]stmt{r.head}, r.conds...) {
			if !m.isBuiltin(st) {
				stmts = append(stmts, st)
			}
		}
	}
	for _, st := range stmts {
		for i, t := range st.args() {
			if t.blank != "" && baseSlot(t.blank) == "fact pattern" {
				label(st.shape().name(), i)
			}
		}
	}
	found := map[string]bool{}
	var patterns []string
	for changed := true; changed; {
		changed = false
		for _, st := range stmts {
			pred := st.shape().name()
			for i, t := range st.args() {
				if t.blank != "" || t.v.isNum || !labels[fmt.Sprintf("%s/%d", pred, i)] || found[t.v.s] {
					continue
				}
				p := t.v.s
				found[p] = true
				patterns = append(patterns, p)
				changed = true
				sh, slots, ok := readPattern(p)
				if !ok {
					continue
				}
				for j, s := range slots {
					if baseSlot(s) == "fact pattern" {
						label(sh.name(), j)
					}
				}
			}
		}
	}
	for _, p := range patterns {
		sh, slots, ok := readPattern(p)
		if !ok {
			continue
		}
		m.emit(self, "[fact pattern] names [predicate]", text(p), text(m.register(sh)))
		for _, s := range slots {
			m.emit(self, "[fact pattern] has the slot [slot]", text(p), text(s))
		}
	}
	for _, r := range m.rules {
		if r.broken {
			continue
		}
		name := text(r.name())
		m.emit(self, "[rule] has the id [id]", name, plainValue(hash16(r.text())))
		if r.rendered() != r.text() || !joinsInOrder(r.joins) {
			m.emit(self, "[rule] is read back differently", name)
		}
		pred := text(r.head.shape().name())
		m.emit(self, "[file] has a rule for [predicate]", text(r.file), pred)
		m.emit(self, "[rule] defines [predicate]", name, pred)
		if r.head.prop == "" && r.head.verb == "breaks" && len(r.head.objs) == 1 && r.head.objs[0].blank == "" {
			m.emit(self, "[rule] lays down [law]", name, r.head.objs[0].v)
		}
		for _, c := range r.conds {
			if !m.isBuiltin(c) {
				m.emit(self, "[rule] refers to [predicate]", name, text(c.shape().name()))
			}
		}
		for _, st := range append([]stmt{r.head}, r.conds...) {
			for _, b := range st.blanks() {
				m.emit(self, "[rule] has the blank [blank]", name, text(b))
			}
		}
	}
	if m.change != "" {
		m.emit(self, "this run is a change")
	}
}

func joinsInOrder(joins []string) bool {
	for i, j := range joins {
		if (i == 0) != (j == "if") {
			return false
		}
	}
	return true
}

func (m *machine) programText() string {
	var b strings.Builder
	defined := map[string]int{}
	referenced := map[string]int{}
	for _, r := range m.rules {
		if r.broken {
			continue
		}
		b.WriteString(r.clause + "\n")
		if r.aux != "" {
			b.WriteString(r.aux + "\n")
		}
		defined[r.head.shape().name()] = r.head.shape().arity
		for _, c := range r.conds {
			if !m.isBuiltin(c) {
				referenced[c.shape().name()] = c.shape().arity
			}
		}
	}
	for _, f := range m.facts {
		var args []string
		for _, a := range f.args {
			args = append(args, a.mangle())
		}
		b.WriteString(f.pred + "(" + strings.Join(args, ", ") + ").\n")
		defined[f.pred] = len(f.args)
	}
	var missing []string
	for p, n := range referenced {
		if _, ok := defined[p]; !ok {
			var vars []string
			for i := 0; i < n; i++ {
				vars = append(vars, fmt.Sprintf("X%d", i))
			}
			missing = append(missing, "Decl "+p+"("+strings.Join(vars, ", ")+").\n")
		}
	}
	sort.Strings(missing)
	return strings.Join(missing, "") + b.String()
}

func solve(src string) (store factstore.SimpleInMemoryStore, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("%v", r)
		}
	}()
	unit, err := parse.Unit(strings.NewReader(src))
	if err != nil {
		return store, err
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		return store, err
	}
	store = factstore.NewSimpleInMemoryStore()
	err = engine.EvalProgram(info, store, engine.WithCreatedFactLimit(20000000))
	return store, err
}

func (m *machine) evaluate() bool {
	store, err := solve(m.programText())
	if err != nil {
		m.problem("the knowledge cannot be worked out: %v", err)
		return false
	}
	known := map[string][][]val{}
	for _, p := range store.ListPredicates() {
		store.GetFacts(ast.NewQuery(p), func(a ast.Atom) error {
			args := make([]val, len(a.Args))
			for i, t := range a.Args {
				if c, ok := t.(ast.Constant); ok {
					args[i] = fromConstant(c)
				} else {
					args[i] = text(t.String())
				}
			}
			known[p.Symbol] = append(known[p.Symbol], args)
			return nil
		})
	}
	for _, rows := range known {
		sort.Slice(rows, func(i, j int) bool { return rowKey(rows[i]) < rowKey(rows[j]) })
	}
	m.known = known
	return true
}

func (m *machine) work() {
	done := map[string]bool{}
	calls := m.predOf("[command] calls [tool] [input]")
	for round := 0; ; round++ {
		if !m.evaluate() {
			return
		}
		var todo [][]val
		for _, c := range m.known[calls] {
			if k := rowKey(c); !done[k] {
				done[k] = true
				todo = append(todo, c)
			}
		}
		if len(todo) == 0 {
			break
		}
		if round > 100 {
			m.problem("the workflow never stops asking for commands")
			return
		}
		for _, r := range m.callAll(todo) {
			m.emit(toolsFile, "[command] returned [field] [value]", r...)
		}
	}
}

func (m *machine) callAll(calls [][]val) [][]val {
	results := make([][][]val, len(calls))
	limit := make(chan struct{}, runtime.NumCPU())
	var wg sync.WaitGroup
	for i, c := range calls {
		wg.Add(1)
		go func(i int, c []val) {
			defer wg.Done()
			limit <- struct{}{}
			defer func() { <-limit }()
			results[i] = m.call(c[0].String(), c[1].String(), c[2].String())
		}(i, c)
	}
	wg.Wait()
	var out [][]val
	for _, r := range results {
		out = append(out, r...)
	}
	return out
}

func (m *machine) explain() {
	have := map[string]bool{}
	for i, r := range m.rules {
		if r.broken {
			continue
		}
		pred := r.head.shape().name()
		if len(r.conds) == 0 {
			if len(r.head.blanks()) > 0 {
				continue
			}
			var args []val
			for _, t := range r.head.args() {
				args = append(args, t.v)
			}
			m.derive(have, pred, args, r.name(), nil)
			continue
		}
		for _, tuple := range m.known[fmt.Sprintf("%s%d", auxPrefix, i)] {
			bind := map[string]val{}
			for j, v := range r.vars {
				bind[v] = tuple[j]
			}
			var args []val
			for _, t := range r.head.fill(bind).args() {
				args = append(args, t.v)
			}
			var reasons []string
			for _, c := range r.conds {
				reasons = append(reasons, c.fill(bind).render())
			}
			m.derive(have, pred, args, r.name(), reasons)
		}
	}
	because := m.predOf("[fact] holds because [reason]")
	seen := map[string]bool{}
	for _, k := range m.objectsOf("[go file] prints [knowledge]", self) {
		for _, p := range m.objectsOf("[knowledge] gives reasons for [fact pattern]", k.String()) {
			pred := m.predOf(p.String())
			for _, d := range m.derivations {
				if d.pred != pred {
					continue
				}
				for _, reason := range d.reasons {
					args := []val{text(d.fact), text(reason)}
					if key := rowKey(args); !seen[key] {
						seen[key] = true
						m.post = append(m.post, fact{because, args, self})
					}
				}
			}
		}
	}
}

func (m *machine) derive(have map[string]bool, pred string, args []val, ruleName string, reasons []string) {
	f := m.line(pred, args)
	id := hash16(strings.Join(append([]string{f, ruleName}, reasons...), "\n"))
	if have[id] {
		return
	}
	have[id] = true
	m.derivations = append(m.derivations, derivation{id, f, hash16(f), pred, ruleName, reasons})
}

func (m *machine) creators() map[string][]string {
	sets := map[string]map[string]bool{}
	add := func(pred, file string) {
		if sets[pred] == nil {
			sets[pred] = map[string]bool{}
		}
		sets[pred][file] = true
	}
	for _, r := range m.rules {
		if !r.broken {
			add(r.head.shape().name(), r.file)
		}
	}
	names := map[string]string{}
	for _, a := range m.factsOf(m.predOf("[fact pattern] names [predicate]")) {
		names[a[0].String()] = a[1].String()
	}
	for _, a := range m.factsOf(m.predOf("[file] creates fact [fact pattern]")) {
		if p, ok := names[a[1].String()]; ok {
			add(p, a[0].String())
		}
	}
	out := map[string][]string{}
	for p, files := range sets {
		for f := range files {
			out[p] = append(out[p], f)
		}
		sort.Strings(out[p])
	}
	return out
}

func (m *machine) checkMade() {
	creators := m.creators()
	for _, f := range append(append([]fact{}, m.facts...), m.post...) {
		ok := false
		for _, c := range creators[f.pred] {
			ok = ok || c == f.by
		}
		if !ok {
			m.problem("%s creates %s facts but nothing says it does", f.by, f.pred)
		}
	}
}

func (m *machine) answer() string {
	var answers []string
	for _, a := range m.factsOf(m.predOf("[folder] conforms [answer]")) {
		answers = append(answers, a[1].String())
	}
	if len(answers) != 1 {
		m.problem("the folder conforms in %d ways", len(answers))
		return ""
	}
	return answers[0]
}

func (m *machine) exitCode(answer string) int {
	for _, a := range m.ordered(m.predOf("[answer] exits with [code]")) {
		if a[0].String() == answer && a[1].isNum {
			return int(a[1].n)
		}
	}
	if answer == brokenAnswer {
		return 2
	}
	return 1
}

type table struct {
	name    string
	columns []string
	rows    [][]any
}

type plan struct {
	path   string
	tables []table
}

func (m *machine) knowledgeNames() []string {
	var out []string
	for _, k := range m.objectsOf("[go file] prints [knowledge]", self) {
		out = append(out, k.String())
	}
	return out
}

func (m *machine) checkPrinting() {
	if len(m.knowledgeNames()) == 0 {
		m.problem("%s has nothing to print", self)
	}
	for _, l := range m.objectsOf("[go file] prints in [language]", self) {
		if l.String() != "plain language" {
			m.problem("%s cannot print in %s", self, l)
		}
	}
	for _, p := range m.objectsOf("[go file] prints to [place]", self) {
		if p.String() != "standard output" {
			m.problem("%s cannot print to %s", self, p)
		}
	}
}

func (m *machine) prepare(answer string) []plan {
	var plans []plan
	for _, k := range m.knowledgeNames() {
		when := m.objectsOf("[knowledge] is published only when [answer]", k)
		allowed := len(when) == 0
		for _, w := range when {
			allowed = allowed || w.String() == answer
		}
		if !allowed {
			continue
		}
		for _, s := range m.objectsOf("[knowledge] is published to [store]", k) {
			paths := m.objectsOf("[store] is the sqlite file [path]", s.String())
			if len(paths) != 1 {
				m.problem("%s is not one sqlite file", s)
				continue
			}
			p := plan{path: paths[0].String()}
			for _, t := range m.objectsOf("[store] has the table [table]", s.String()) {
				if tb, ok := m.buildTable(t.String(), answer); ok {
					p.tables = append(p.tables, tb)
				}
			}
			plans = append(plans, p)
		}
	}
	return plans
}

func (m *machine) buildTable(name, answer string) (table, bool) {
	kinds := m.objectsOf("[table] has a row for [kind]", name)
	if len(kinds) != 1 {
		m.problem("the table %s does not have one kind of row", name)
		return table{}, false
	}
	rows, ok := m.rowsFor(kinds[0].String(), answer)
	if !ok {
		m.problem("%s cannot make a row for %s", self, kinds[0])
		return table{}, false
	}
	type column struct {
		pos     int64
		name    string
		meaning string
	}
	var cols []column
	for _, a := range m.factsOf(m.predOf("[table] has the column [position] [column] [meaning]")) {
		if a[0].String() == name {
			cols = append(cols, column{a[1].n, a[2].String(), a[3].String()})
		}
	}
	sort.Slice(cols, func(i, j int) bool { return cols[i].pos < cols[j].pos })
	t := table{name: name}
	for _, c := range cols {
		t.columns = append(t.columns, c.name)
	}
	for _, r := range rows {
		var out []any
		for _, c := range cols {
			v, ok := r[c.meaning]
			if !ok {
				m.problem("%s does not know %s for %s", self, c.meaning, kinds[0])
				return table{}, false
			}
			out = append(out, v)
		}
		t.rows = append(t.rows, out)
	}
	return t, true
}

func (m *machine) rowsFor(kind, answer string) ([]map[string]any, bool) {
	var rows []map[string]any
	switch kind {
	case "every rule":
		in := map[string]bool{}
		for _, a := range m.factsOf(m.predOf("[rule] is in the knowledge")) {
			in[a[0].String()] = true
		}
		for _, r := range m.rules {
			if !in[r.name()] {
				continue
			}
			rows = append(rows, map[string]any{
				"the rule id":             hash16(r.text()),
				"the rule name":           r.name(),
				"the file the rule is in": r.file,
				"the number of the line the rule starts on": int64(r.line),
				"the rule lines joined by newlines":         r.text(),
			})
		}
	case "every fact":
		creators := m.creators()
		for _, f := range m.allFacts() {
			l := m.line(f.pred, f.args)
			rows = append(rows, map[string]any{
				"the fact id":                hash16(l),
				"the fact as one plain line": l,
				"the file that creates the predicate of the fact": strings.Join(creators[f.pred], ", "),
			})
		}
	case "every way a rule derives a fact":
		for _, d := range m.derivations {
			rows = append(rows, map[string]any{
				"the derivation id": d.id,
				"the fact id":       d.factID,
				"the rule name":     d.rule,
			})
		}
	case "every reason of every derivation":
		for _, d := range m.derivations {
			for i, r := range d.reasons {
				rows = append(rows, map[string]any{
					"the derivation id":                                      d.id,
					"the number of the condition in the rule":                int64(i + 1),
					"the condition with its blanks filled as one plain line": r,
				})
			}
		}
	case "every part the certificate holds":
		for _, a := range m.factsOf(m.predOf("[certificate] holds [part]")) {
			part := a[1].String()
			what := "what the certificate holds"
			subject := "the file a hash is of and empty for the answer"
			value := "the sha256 of the file in hex or the answer"
			switch part {
			case "the hash of every file " + self + " loads":
				for _, f := range m.loaded {
					rows = append(rows, map[string]any{what: part, subject: f, value: m.hashes[f]})
				}
			case "the answer":
				rows = append(rows, map[string]any{what: part, subject: "", value: answer})
			default:
				m.problem("the certificate cannot hold %s", part)
			}
		}
	default:
		return nil, false
	}
	return rows, true
}

func (m *machine) allFacts() []fact {
	var out []fact
	var preds []string
	for p := range m.known {
		if !strings.Contains(p, "__") {
			preds = append(preds, p)
		}
	}
	sort.Strings(preds)
	for _, p := range preds {
		for _, a := range m.known[p] {
			out = append(out, fact{pred: p, args: a})
		}
	}
	return append(out, m.post...)
}

func publish(p plan) error {
	next := p.path + ".next"
	os.Remove(next)
	db, err := sql.Open("sqlite", next)
	if err != nil {
		return err
	}
	err = fill(db, p.tables)
	if cerr := db.Close(); err == nil {
		err = cerr
	}
	if err != nil {
		os.Remove(next)
		return err
	}
	return os.Rename(next, p.path)
}

func fill(db *sql.DB, tables []table) error {
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	for _, t := range tables {
		var cols, marks []string
		for _, c := range t.columns {
			cols = append(cols, ident(c))
			marks = append(marks, "?")
		}
		if _, err := tx.Exec("CREATE TABLE " + ident(t.name) + " (" + strings.Join(cols, ", ") + ")"); err != nil {
			tx.Rollback()
			return err
		}
		insert := "INSERT INTO " + ident(t.name) + " VALUES (" + strings.Join(marks, ", ") + ")"
		for _, r := range t.rows {
			if _, err := tx.Exec(insert, r...); err != nil {
				tx.Rollback()
				return err
			}
		}
	}
	return tx.Commit()
}

func ident(s string) string {
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func (m *machine) shownLines() []string {
	var out []string
	seen := map[string]bool{}
	for _, k := range m.knowledgeNames() {
		var preds []string
		for _, p := range m.objectsOf("[knowledge] shows [fact pattern]", k) {
			if pred := m.predOf(p.String()); pred != "" && !seen[pred] {
				seen[pred] = true
				preds = append(preds, pred)
			}
		}
		sort.Strings(preds)
		for _, pred := range preds {
			var lines []string
			for _, a := range m.factsOf(pred) {
				lines = append(lines, m.line(pred, a))
			}
			sort.Strings(lines)
			out = append(out, lines...)
		}
	}
	return out
}

func (m *machine) problemLines() []string {
	pred := m.predOf("[text] is a problem")
	var out []string
	for _, p := range m.problems {
		out = append(out, m.line(pred, []val{text(p)}))
	}
	return out
}

func (m *machine) run() int {
	m.load()
	m.learnMangle()
	m.translate()
	m.describe()
	if len(m.problems) == 0 {
		m.work()
	}
	answer := ""
	var plans []plan
	if len(m.problems) == 0 {
		m.explain()
		m.checkMade()
		m.checkPrinting()
		answer = m.answer()
		plans = m.prepare(answer)
	}
	if len(m.problems) > 0 {
		for _, l := range m.problemLines() {
			fmt.Println(l)
		}
		return m.exitCode(brokenAnswer)
	}
	for _, l := range m.shownLines() {
		fmt.Println(l)
	}
	for _, p := range plans {
		if err := publish(p); err != nil {
			m.problem("the knowledge cannot be published to %s: %v", p.path, err)
			for _, l := range m.problemLines() {
				fmt.Println(l)
			}
			return m.exitCode(brokenAnswer)
		}
	}
	return m.exitCode(answer)
}

func main() {
	m := newMachine()
	if len(os.Args) > 1 {
		m.change = os.Args[1]
	}
	os.Exit(m.run())
}
