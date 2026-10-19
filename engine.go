package main

import (
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	"codeberg.org/TauCeti/mangle-go/unionfind"
	_ "modernc.org/sqlite"
)

const (
	thisFile       = "engine.go"
	entryFile      = "spec.plain"
	changeVariable = "MACHINE_CHANGE"
	plainKind      = "rules and facts"
	rowsKind       = "a row per line with a cell per column"
	broken         = "broken"
)

var (
	blankShape  = regexp.MustCompile(`^\[([a-z0-9]+(?: [a-z0-9]+)*)\]$`)
	numberShape = regexp.MustCompile(`^(?:0|-?[1-9][0-9]{0,17})$`)
	wordsShape  = regexp.MustCompile(`^[a-z][a-z0-9]*(?: [a-z0-9]+)*$`)
	slotShape   = regexp.MustCompile(`\[([^\[\]]*)\]`)
)

var methods = map[string]string{
	"a rule id":    "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":    "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a row name":   "the file name and a colon and the line number",
	"a cell value": "the cell text read as a plain value",
}

type term struct {
	blank string
	text  string
	num   int64
	isNum bool
}

func word(s string) term { return term{text: s} }

func count(n int64) term { return term{num: n, isNum: true} }

func plainValue(s string) term {
	if numberShape.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return count(n)
		}
	}
	return word(s)
}

func (t term) value() string {
	if t.isNum {
		return strconv.FormatInt(t.num, 10)
	}
	return t.text
}

func (t term) plain() string {
	switch {
	case t.blank != "":
		return "[" + t.blank + "]"
	case t.isNum:
		return strconv.FormatInt(t.num, 10)
	}
	return quoted(t.text)
}

func (t term) mangle() string {
	switch {
	case t.blank != "":
		return variable(t.blank)
	case t.isNum:
		return strconv.FormatInt(t.num, 10)
	}
	return ast.String(t.text).String()
}

func (t term) constant() ast.Constant {
	if t.isNum {
		return ast.Number(t.num)
	}
	return ast.String(t.text)
}

func fromMangleTerm(b ast.BaseTerm) term {
	c, ok := b.(ast.Constant)
	if !ok {
		return word(b.String())
	}
	switch c.Type {
	case ast.NumberType:
		return count(c.NumValue)
	case ast.StringType:
		return word(c.Symbol)
	}
	return word(c.String())
}

func quoted(s string) string {
	if !needsQuotes(s) {
		return s
	}
	if strings.Contains(s, `"`) {
		return "'" + s + "'"
	}
	return `"` + s + `"`
}

func needsQuotes(s string) bool {
	return s == "" || strings.Contains(s, ", ") || strings.ContainsAny(s, "\r\n") ||
		s[0] == '"' || s[0] == '\'' || strings.TrimSpace(s) != s ||
		numberShape.MatchString(s) || blankShape.MatchString(s) || strings.HasPrefix(s, "not ")
}

func variable(blank string) string {
	var b strings.Builder
	for _, w := range strings.Fields(blank) {
		b.WriteString(strings.ToUpper(w[:1]) + w[1:])
	}
	return b.String()
}

func shortHash(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])[:16]
}

const (
	proposition = iota
	property
	relation
)

type form struct {
	kind  int
	words string
}

func (f form) name() string { return strings.ReplaceAll(f.words, " ", "_") }

func predicateKey(name string, arity int) string { return name + "/" + strconv.Itoa(arity) }

type atom struct {
	form form
	args []term
	neg  bool
}

func fact(words string, args ...term) atom {
	kind := relation
	switch len(args) {
	case 0:
		kind = proposition
	case 1:
		kind = property
	}
	return atom{form: form{kind, words}, args: args}
}

func (a atom) key() string { return predicateKey(a.form.name(), len(a.args)) }

func (a atom) plain() string {
	var s string
	switch a.form.kind {
	case proposition:
		s = a.form.words
	case property:
		s = a.args[0].plain() + ", is, " + a.form.words
	default:
		parts := []string{a.args[0].plain(), a.form.words}
		for _, t := range a.args[1:] {
			parts = append(parts, t.plain())
		}
		s = strings.Join(parts, ", ")
	}
	if a.neg {
		return "not " + s
	}
	return s
}

func (a atom) mangle() string {
	args := make([]string, len(a.args))
	for i, t := range a.args {
		args[i] = t.mangle()
	}
	return a.form.name() + "(" + strings.Join(args, ", ") + ")"
}

func (a atom) toMangle() ast.Atom {
	args := make([]ast.BaseTerm, len(a.args))
	for i, t := range a.args {
		args[i] = t.constant()
	}
	return ast.NewAtom(a.form.name(), args...)
}

func (a atom) ground() bool {
	for _, t := range a.args {
		if t.blank != "" {
			return false
		}
	}
	return true
}

type part struct {
	text   string
	quoted bool
}

func (p part) term() term {
	if p.quoted {
		return word(p.text)
	}
	if m := blankShape.FindStringSubmatch(p.text); m != nil {
		return term{blank: m[1]}
	}
	return plainValue(p.text)
}

func splitParts(s string) ([]part, error) {
	var parts []part
	for {
		if s == "" {
			return nil, errors.New("a part is empty")
		}
		if s[0] == '"' || s[0] == '\'' {
			end := -1
			for j := 1; j < len(s); j++ {
				if s[j] == s[0] && (j == len(s)-1 || strings.HasPrefix(s[j+1:], ", ")) {
					end = j
					break
				}
			}
			if end < 0 {
				return nil, fmt.Errorf("the quote in %s is never closed", s)
			}
			parts = append(parts, part{s[1:end], true})
			if end == len(s)-1 {
				return parts, nil
			}
			s = s[end+3:]
			continue
		}
		i := strings.Index(s, ", ")
		if i == 0 {
			return nil, errors.New("a part is empty")
		}
		if i < 0 {
			return append(parts, part{s, false}), nil
		}
		parts = append(parts, part{s[:i], false})
		s = s[i+2:]
	}
}

func parseAtom(s string) (atom, error) {
	parts, err := splitParts(s)
	if err != nil {
		return atom{}, err
	}
	switch len(parts) {
	case 1:
		if parts[0].quoted || !wordsShape.MatchString(parts[0].text) {
			return atom{}, fmt.Errorf("%s is neither a fact nor a proposition", quoted(s))
		}
		return atom{form: form{proposition, parts[0].text}}, nil
	case 2:
		return atom{}, fmt.Errorf("%s has a subject and a verb but no object", quoted(s))
	}
	verb := parts[1]
	if verb.quoted || !wordsShape.MatchString(verb.text) {
		return atom{}, fmt.Errorf("%s is not a verb", quoted(verb.text))
	}
	if verb.text == "is" && len(parts) == 3 && !parts[2].quoted {
		object := parts[2].term()
		if object.blank == "" && !object.isNum {
			if !wordsShape.MatchString(object.text) {
				return atom{}, fmt.Errorf("%s cannot name a property", quoted(object.text))
			}
			return atom{form: form{property, object.text}, args: []term{parts[0].term()}}, nil
		}
	}
	args := []term{parts[0].term()}
	for _, p := range parts[2:] {
		args = append(args, p.term())
	}
	return atom{form: form{relation, verb.text}, args: args}, nil
}

type pattern struct {
	form  form
	slots []string
}

func parsePattern(s string) (pattern, error) {
	bad := fmt.Errorf("%s is not a fact pattern", quoted(s))
	locs := slotShape.FindAllStringSubmatchIndex(s, -1)
	if len(locs) == 0 {
		if !wordsShape.MatchString(s) {
			return pattern{}, bad
		}
		return pattern{form: form{proposition, s}}, nil
	}
	if locs[0][0] != 0 {
		return pattern{}, bad
	}
	var slots []string
	for _, l := range locs {
		slot := s[l[2]:l[3]]
		if !blankShape.MatchString("[" + slot + "]") {
			return pattern{}, bad
		}
		slots = append(slots, slot)
	}
	if len(locs) == 1 {
		tail := s[locs[0][1]:]
		words := strings.TrimPrefix(tail, " is ")
		if words == tail || !wordsShape.MatchString(words) {
			return pattern{}, bad
		}
		return pattern{form{property, words}, slots}, nil
	}
	between := s[locs[0][1]:locs[1][0]]
	words := strings.TrimSpace(between)
	if between != " "+words+" " || !wordsShape.MatchString(words) || locs[len(locs)-1][1] != len(s) {
		return pattern{}, bad
	}
	for i := 2; i < len(locs); i++ {
		if s[locs[i-1][1]:locs[i][0]] != " " {
			return pattern{}, bad
		}
	}
	return pattern{form{relation, words}, slots}, nil
}

func (p pattern) key() string { return predicateKey(p.form.name(), len(p.slots)) }

type rule struct {
	file  string
	line  int
	index int
	lines []string
	head  atom
	conds []atom
}

func (r *rule) name() string { return fmt.Sprintf("%s:%d", r.file, r.line) }

func (r *rule) id() string { return shortHash(strings.Join(r.lines, "\n")) }

func (r *rule) plain() string {
	lines := []string{r.head.plain()}
	for i, c := range r.conds {
		lead := "    and "
		if i == 0 {
			lead = "    if "
		}
		lines = append(lines, lead+c.plain())
	}
	return strings.Join(lines, "\n")
}

func (r *rule) blanks() []string {
	var out []string
	seen := map[string]bool{}
	for _, a := range append([]atom{r.head}, r.conds...) {
		for _, t := range a.args {
			if t.blank != "" && !seen[t.blank] {
				seen[t.blank] = true
				out = append(out, t.blank)
			}
		}
	}
	return out
}

type template struct {
	vars []string
	text string
}

func identifierByte(c byte) bool {
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

func (t template) expand(args []term) string {
	values := map[string]string{}
	for i, v := range t.vars {
		values[v] = args[i].mangle()
	}
	var b strings.Builder
	s := t.text
	for i := 0; i < len(s); {
		c := s[i]
		switch {
		case c == '"' || c == '\'' || c == '`':
			j := i + 1
			for j < len(s) && s[j] != c {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			j = min(j+1, len(s))
			b.WriteString(s[i:j])
			i = j
		case identifierByte(c):
			j := i
			for j < len(s) && identifierByte(s[j]) {
				j++
			}
			id := s[i:j]
			if v, ok := values[id]; ok && (i == 0 || s[i-1] != ':') {
				b.WriteString(v)
			} else {
				b.WriteString(id)
			}
			i = j
		default:
			b.WriteByte(c)
			i++
		}
	}
	return b.String()
}

type derivation struct {
	rule    *rule
	reasons []string
	negated []bool
}

type machine struct {
	problems  []string
	rules     []*rule
	base      []atom
	baseSeen  map[string]bool
	returned  []atom
	extra     []atom
	forms     map[string]form
	loaded    []string
	hashes    map[string]string
	templates map[string]template
	ground    map[string]int
	unit      parse.SourceUnit
	bodies    []*rule
	decls     map[ast.PredicateSym]ast.Decl
	clauses   map[string]*rule
	derived   map[string][]derivation
	seen      map[string]bool
	out       strings.Builder
}

func newMachine() *machine {
	return &machine{
		baseSeen:  map[string]bool{},
		forms:     map[string]form{},
		hashes:    map[string]string{},
		templates: map[string]template{},
		ground:    map[string]int{},
		derived:   map[string][]derivation{},
		seen:      map[string]bool{},
	}
}

func (m *machine) problem(format string, args ...any) {
	m.problems = append(m.problems, fmt.Sprintf(format, args...))
}

func (m *machine) learn(a atom) {
	if _, ok := m.forms[a.key()]; !ok {
		m.forms[a.key()] = a.form
	}
}

func (m *machine) add(a atom) {
	text := a.plain()
	if m.baseSeen[text] {
		return
	}
	m.baseSeen[text] = true
	m.learn(a)
	m.base = append(m.base, a)
}

func (m *machine) groundFacts(name string, arity int) [][]term {
	var out [][]term
	for _, r := range m.rules {
		if len(r.conds) == 0 && r.head.form.name() == name && len(r.head.args) == arity && r.head.ground() {
			out = append(out, r.head.args)
		}
	}
	return out
}

func (m *machine) load() {
	queue := []string{entryFile}
	seen := map[string]bool{}
	for len(queue) > 0 {
		file := queue[0]
		queue = queue[1:]
		if seen[file] || filepath.Base(file) != file {
			continue
		}
		seen[file] = true
		data, err := os.ReadFile(file)
		if err != nil {
			if !errors.Is(err, fs.ErrNotExist) {
				m.problem("%s cannot read %s: %v", thisFile, file, err)
			}
			continue
		}
		kind := plainKind
		if len(m.loaded) > 0 {
			kind = m.kindOf(file)
		}
		m.loaded = append(m.loaded, file)
		sum := sha256.Sum256(data)
		m.hashes[file] = hex.EncodeToString(sum[:])
		switch kind {
		case plainKind:
			m.readPlain(file, string(data))
		case rowsKind:
			m.readRows(file, string(data))
		case "":
			m.problem("%s does not know what language %s is written in", thisFile, file)
		default:
			m.problem("%s cannot load %s as %s", thisFile, file, kind)
		}
		for _, args := range m.groundFacts("loads", 2) {
			if args[0].value() == thisFile && !args[1].isNum {
				queue = append(queue, args[1].text)
			}
		}
	}
	if len(m.loaded) == 0 {
		m.problem("%s is not in the folder", entryFile)
	}
}

func (m *machine) kindOf(file string) string {
	ending, language := "", ""
	for _, args := range m.groundFacts("means", 2) {
		e := args[0].value()
		if strings.HasSuffix(file, e) && len(e) > len(ending) {
			ending, language = e, args[1].value()
		}
	}
	if language == "" {
		return ""
	}
	for _, args := range m.groundFacts("is_loaded_as", 2) {
		if args[0].value() == language {
			return args[1].value()
		}
	}
	return ""
}

func (m *machine) readPlain(file, content string) {
	var current *rule
	for i, line := range strings.Split(content, "\n") {
		where := fmt.Sprintf("%s:%d", file, i+1)
		if strings.TrimSpace(line) == "" {
			current = nil
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			text := strings.TrimLeft(line, " \t")
			var body string
			switch {
			case strings.HasPrefix(text, "if "):
				body = text[3:]
			case strings.HasPrefix(text, "and "):
				body = text[4:]
			default:
				m.problem("%s: %s is neither a rule nor a condition", where, quoted(line))
				continue
			}
			if current == nil {
				m.problem("%s: %s is a condition of no rule", where, quoted(line))
				continue
			}
			negated := strings.HasPrefix(body, "not ")
			body = strings.TrimPrefix(body, "not ")
			a, err := parseAtom(body)
			if err != nil {
				m.problem("%s: %v", where, err)
				continue
			}
			a.neg = negated
			current.conds = append(current.conds, a)
			current.lines = append(current.lines, line)
			continue
		}
		a, err := parseAtom(line)
		if err != nil {
			m.problem("%s: %v", where, err)
			current = nil
			continue
		}
		current = &rule{file: file, line: i + 1, index: len(m.rules), lines: []string{line}, head: a}
		m.rules = append(m.rules, current)
	}
}

func (m *machine) readRows(file, content string) {
	var header []string
	for i, line := range strings.Split(content, "\n") {
		if strings.TrimSpace(line) == "" {
			continue
		}
		where := fmt.Sprintf("%s:%d", file, i+1)
		cells, err := csv.NewReader(strings.NewReader(line)).Read()
		if err != nil {
			m.problem("%s: %v", where, err)
			continue
		}
		if header == nil {
			header = cells
			continue
		}
		if len(cells) != len(header) {
			m.problem("%s: has %d cells but the header names %d columns", where, len(cells), len(header))
			continue
		}
		row := word(where)
		m.add(fact("is a row of", row, plainValue(file)))
		for j, column := range header {
			m.add(fact("has the cell", row, plainValue(column), plainValue(cells[j])))
		}
	}
}

func (m *machine) prepare() {
	if os.Getenv(changeVariable) != "" {
		m.add(fact("this run is a change"))
	}
	for _, r := range m.rules {
		m.learn(r.head)
		for _, c := range r.conds {
			m.learn(c)
		}
		if len(r.conds) == 0 && r.head.ground() {
			if _, ok := m.ground[r.head.plain()]; !ok {
				m.ground[r.head.plain()] = r.index
			}
		}
	}
	for _, args := range m.groundFacts("is_computed_as", 2) {
		if want, ok := methods[args[0].value()]; !ok || want != args[1].value() {
			m.problem("%s does not compute %s as %s", thisFile, args[0].value(), args[1].value())
		}
	}
	for _, r := range m.rules {
		name := word(r.name())
		predicate := word(r.head.form.name())
		m.add(fact("has the id", name, plainValue(r.id())))
		m.add(fact("has a rule for", plainValue(r.file), predicate))
		m.add(fact("defines", name, predicate))
		for _, c := range r.conds {
			m.add(fact("refers to", name, word(c.form.name())))
		}
		if r.head.form.kind == relation && r.head.form.words == "breaks" && len(r.head.args) == 2 && r.head.args[1].blank == "" {
			m.add(fact("lays down", name, r.head.args[1]))
		}
		for _, b := range r.blanks() {
			m.add(fact("has the blank", name, word(b)))
		}
		if r.plain() != strings.Join(r.lines, "\n") {
			m.add(fact("read back differently", name))
		}
	}
	m.findPatterns()
	m.readTemplates()
	m.checkCreated(thisFile, m.base)
}

func (m *machine) declared(file string) map[string]bool {
	out := map[string]bool{}
	for _, args := range m.groundFacts("creates_fact", 2) {
		if args[0].value() != file || args[1].isNum {
			continue
		}
		if p, err := parsePattern(args[1].text); err == nil {
			out[p.key()] = true
		}
	}
	return out
}

func (m *machine) checkCreated(file string, atoms []atom) {
	declared := m.declared(file)
	reported := map[string]bool{}
	for _, a := range atoms {
		if !declared[a.key()] && !reported[a.key()] {
			reported[a.key()] = true
			m.problem("%s would create %s facts, but nothing says it creates them", file, quoted(a.form.words))
		}
	}
}

func (m *machine) findPatterns() {
	positions := map[string][]int{predicateKey("executes_instruction", 2): {1}}
	for _, args := range m.groundFacts("executes_instruction", 2) {
		if args[1].isNum {
			continue
		}
		p, err := parsePattern(args[1].text)
		if err != nil {
			continue
		}
		for i, s := range p.slots {
			if s == "fact pattern" && !slices.Contains(positions[p.key()], i) {
				positions[p.key()] = append(positions[p.key()], i)
			}
		}
	}
	seen := map[string]bool{}
	for _, r := range m.rules {
		for _, i := range positions[r.head.key()] {
			t := r.head.args[i]
			if t.blank != "" || t.isNum || seen[t.text] {
				continue
			}
			seen[t.text] = true
			p, err := parsePattern(t.text)
			if err != nil {
				m.problem("%s: %v", r.name(), err)
				continue
			}
			m.learn(atom{form: p.form, args: make([]term, len(p.slots))})
			m.add(fact("names", t, word(p.form.name())))
			for _, s := range p.slots {
				m.add(fact("has the slot", t, word(s)))
			}
		}
	}
}

func (m *machine) readTemplates() {
	meanings := m.groundFacts("means_in_mangle", 2)
	for _, args := range meanings {
		a, err := parseAtom(args[0].value())
		text := args[1].value()
		if err != nil || len(a.args) == 0 || strings.HasSuffix(text, ".") {
			continue
		}
		var vars []string
		distinct := map[string]bool{}
		for _, t := range a.args {
			if t.blank == "" || distinct[t.blank] {
				vars = nil
				break
			}
			distinct[t.blank] = true
			vars = append(vars, variable(t.blank))
		}
		if len(vars) == len(a.args) {
			m.templates[a.key()] = template{vars, text}
		}
	}
	for _, args := range meanings {
		line, text := args[0].value(), args[1].value()
		got, err := m.lineInMangle(line)
		if err != nil {
			m.problem("%s cannot read %s: %v", thisFile, quoted(line), err)
			continue
		}
		if got != text {
			m.problem("%s means in mangle %s, but %s reads it as %s", quoted(line), quoted(text), thisFile, quoted(got))
		}
	}
}

func (m *machine) lineInMangle(line string) (string, error) {
	a, err := parseAtom(line)
	if err != nil {
		return "", err
	}
	if t, ok := m.templates[a.key()]; ok {
		return t.expand(a.args), nil
	}
	return a.mangle() + ".", nil
}

func (m *machine) clauseText(r *rule) (string, error) {
	if _, ok := m.templates[r.head.key()]; ok {
		return "", fmt.Errorf("%s cannot be concluded, it is a builtin", quoted(r.head.form.words))
	}
	head := r.head.mangle()
	if len(r.conds) == 0 {
		return head + ".", nil
	}
	var body []string
	for _, c := range r.conds {
		if t, ok := m.templates[c.key()]; ok {
			if c.neg {
				return "", fmt.Errorf("the builtin %s cannot be negated", quoted(c.form.words))
			}
			body = append(body, t.expand(c.args))
			continue
		}
		s := c.mangle()
		if c.neg {
			s = "!" + s
		}
		body = append(body, s)
	}
	return head + " :- " + strings.Join(body, ", ") + ".", nil
}

func (m *machine) compile() {
	defined := map[string]bool{}
	needed := map[string]ast.PredicateSym{}
	need := func(a atom) {
		needed[a.key()] = ast.PredicateSym{Symbol: a.form.name(), Arity: len(a.args)}
	}
	for _, r := range m.rules {
		text, err := m.clauseText(r)
		if err != nil {
			m.problem("%s: %v", r.name(), err)
			continue
		}
		c, err := parse.Clause(text)
		if err != nil {
			m.problem("%s: mangle cannot read %s: %v", r.name(), text, err)
			continue
		}
		m.unit.Clauses = append(m.unit.Clauses, c)
		defined[r.head.key()] = true
		if len(r.conds) > 0 {
			m.bodies = append(m.bodies, r)
		}
		for _, c := range r.conds {
			if _, ok := m.templates[c.key()]; !ok {
				need(c)
			}
		}
	}
	for _, a := range m.base {
		need(a)
	}
	need(fact("returned", word(""), word(""), word("")))
	m.decls = map[ast.PredicateSym]ast.Decl{}
	for key, sym := range needed {
		if !defined[key] {
			m.decls[sym] = ast.NewSyntheticDeclFromSym(sym)
		}
	}
}

type recorder struct{ m *machine }

func (r recorder) RuleFired(clause ast.Clause, head ast.Atom, subst unionfind.UnionFind, _ []ast.Atom) {
	m := r.m
	ru := m.clauses[clause.String()]
	if ru == nil {
		return
	}
	text := m.fromMangle(head).plain()
	reasons := make([]string, len(ru.conds))
	negated := make([]bool, len(ru.conds))
	for i, c := range ru.conds {
		reasons[i] = instantiate(c, subst).plain()
		negated[i] = c.neg
	}
	key := ru.name() + "\x00" + text + "\x00" + strings.Join(reasons, "\x00")
	if m.seen[key] {
		return
	}
	m.seen[key] = true
	m.derived[text] = append(m.derived[text], derivation{ru, reasons, negated})
}

func (recorder) LetEmit(ast.Clause, ast.Atom, ast.ConstSubstList, ast.Atom) {}

func (recorder) DoEmit(ast.Clause, ast.Atom, []ast.Constant, []ast.Atom, ast.Atom) {}

func instantiate(c atom, subst unionfind.UnionFind) atom {
	out := atom{form: c.form, neg: c.neg, args: make([]term, len(c.args))}
	for i, t := range c.args {
		out.args[i] = t
		if t.blank == "" {
			continue
		}
		if v, ok := subst.Get(ast.Variable{Symbol: variable(t.blank)}).(ast.Constant); ok {
			out.args[i] = fromMangleTerm(v)
		}
	}
	return out
}

func (m *machine) fromMangle(a ast.Atom) atom {
	key := predicateKey(a.Predicate.Symbol, a.Predicate.Arity)
	f, ok := m.forms[key]
	if !ok {
		f = form{relation, strings.ReplaceAll(a.Predicate.Symbol, "_", " ")}
	}
	out := atom{form: f, args: make([]term, len(a.Args))}
	for i, t := range a.Args {
		out.args[i] = fromMangleTerm(t)
	}
	return out
}

func (m *machine) evaluate(record bool) (factstore.FactStore, error) {
	info, err := analysis.AnalyzeOneUnit(m.unit, m.decls)
	if err != nil {
		return nil, err
	}
	var options []engine.EvalOption
	if record {
		if len(info.Rules) != len(m.bodies) {
			return nil, fmt.Errorf("mangle kept %d of %d rules", len(info.Rules), len(m.bodies))
		}
		m.clauses = map[string]*rule{}
		for i, c := range info.Rules {
			if _, ok := m.clauses[c.String()]; !ok {
				m.clauses[c.String()] = m.bodies[i]
			}
		}
		options = append(options, engine.WithDerivationRecorder(recorder{m}))
	}
	store := factstore.NewSimpleInMemoryStore()
	for _, a := range m.base {
		store.Add(a.toMangle())
	}
	for _, a := range m.returned {
		store.Add(a.toMangle())
	}
	if err := engine.EvalProgram(info, store, options...); err != nil {
		return nil, err
	}
	return store, nil
}

type knowledge struct {
	m     *machine
	store factstore.FactStore
}

func (m *machine) position(text string) int {
	best := len(m.rules) + 1
	if i, ok := m.ground[text]; ok {
		best = i
	}
	for _, d := range m.derived[text] {
		best = min(best, d.rule.index)
	}
	return best
}

func (m *machine) sorted(atoms []atom) []atom {
	sort.SliceStable(atoms, func(i, j int) bool {
		a, b := atoms[i].plain(), atoms[j].plain()
		pa, pb := m.position(a), m.position(b)
		if pa != pb {
			return pa < pb
		}
		return a < b
	})
	return atoms
}

func (k *knowledge) atoms(name string, arity int) []atom {
	var out []atom
	k.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: name, Arity: arity}), func(a ast.Atom) error {
		out = append(out, k.m.fromMangle(a))
		return nil
	})
	for _, a := range k.m.extra {
		if a.form.name() == name && len(a.args) == arity {
			out = append(out, a)
		}
	}
	return k.m.sorted(out)
}

func (k *knowledge) facts(name string, arity int) [][]term {
	var out [][]term
	for _, a := range k.atoms(name, arity) {
		out = append(out, a.args)
	}
	return out
}

func (k *knowledge) values(name, subject string) []string {
	var out []string
	for _, args := range k.facts(name, 2) {
		if args[0].value() == subject {
			out = append(out, args[1].value())
		}
	}
	return out
}

func (m *machine) execute() bool {
	done := map[string]bool{}
	for round := 0; ; round++ {
		if round == 100 {
			m.problem("the commands never stop calling new commands")
			return false
		}
		store, err := m.evaluate(false)
		if err != nil {
			m.problem("mangle cannot evaluate the knowledge: %v", err)
			return false
		}
		k := &knowledge{m, store}
		var todo []call
		for _, args := range k.facts("calls", 3) {
			c := call{args[0], args[1], args[2]}
			key := c.command.plain() + "\x00" + c.tool.plain() + "\x00" + c.input.plain()
			if !done[key] {
				done[key] = true
				todo = append(todo, c)
			}
		}
		if len(todo) == 0 {
			return true
		}
		results := make([][]atom, len(todo))
		slots := make(chan struct{}, runtime.NumCPU())
		var wg sync.WaitGroup
		for i, c := range todo {
			wg.Add(1)
			go func() {
				defer wg.Done()
				slots <- struct{}{}
				defer func() { <-slots }()
				results[i] = runCommand(c, k)
			}()
		}
		wg.Wait()
		for _, r := range results {
			m.checkCreated(toolsFile, r)
			m.returned = append(m.returned, r...)
		}
		if len(m.problems) > 0 {
			return false
		}
	}
}

func (m *machine) explain(k *knowledge, view string) {
	added := map[string]bool{}
	for _, p := range k.values("gives_reasons_for", view) {
		pat, err := parsePattern(p)
		if err != nil {
			m.problem("%v", err)
			continue
		}
		for _, a := range k.atoms(pat.form.name(), len(pat.slots)) {
			text := a.plain()
			for _, d := range m.derived[text] {
				for _, reason := range d.reasons {
					hb := fact("holds because", word(text), word(reason))
					if !added[hb.plain()] {
						added[hb.plain()] = true
						m.learn(hb)
						m.extra = append(m.extra, hb)
					}
				}
			}
		}
	}
	m.checkCreated(thisFile, m.extra)
}

func (m *machine) print(k *knowledge, view string) {
	if !slices.Contains(k.values("prints_in", thisFile), "plain language") {
		m.problem("%s prints only in plain language", thisFile)
		return
	}
	if !slices.Contains(k.values("prints_to", thisFile), "standard output") {
		m.problem("%s prints only to standard output", thisFile)
		return
	}
	shown := k.values("shows", view)
	reasoned := map[string]bool{}
	for _, p := range k.values("gives_reasons_for", view) {
		reasoned[p] = slices.Contains(shown, p)
	}
	because := map[string][]string{}
	inline := map[string]bool{}
	for _, a := range m.extra {
		if a.key() == predicateKey("holds_because", 2) {
			because[a.args[0].text] = append(because[a.args[0].text], a.plain())
		}
	}
	for _, p := range shown {
		pat, err := parsePattern(p)
		if err != nil || !reasoned[p] {
			continue
		}
		for _, a := range k.atoms(pat.form.name(), len(pat.slots)) {
			for _, line := range because[a.plain()] {
				inline[line] = true
			}
		}
	}
	printed := map[string]bool{}
	emit := func(line string) {
		if !printed[line] {
			printed[line] = true
			m.out.WriteString(line + "\n")
		}
	}
	for _, p := range shown {
		pat, err := parsePattern(p)
		if err != nil {
			m.problem("%v", err)
			continue
		}
		for _, a := range k.atoms(pat.form.name(), len(pat.slots)) {
			line := a.plain()
			if inline[line] {
				continue
			}
			emit(line)
			if reasoned[p] {
				for _, reason := range because[line] {
					emit(reason)
				}
			}
		}
	}
}

func (m *machine) exitCode(k *knowledge, answer string) int {
	var codes [][]term
	if k != nil {
		codes = k.facts("exits_with", 2)
	} else {
		codes = m.groundFacts("exits_with", 2)
	}
	for _, args := range codes {
		if args[0].value() == answer && args[1].isNum {
			return int(args[1].num)
		}
	}
	return 2
}

func (m *machine) fail(k *knowledge) int {
	for _, p := range m.problems {
		m.out.WriteString(fact("a problem", word(p)).plain() + "\n")
	}
	os.Stdout.WriteString(m.out.String())
	return m.exitCode(k, broken)
}

func (m *machine) answer(k *knowledge) string {
	var answers []string
	for _, args := range k.facts("conforms", 2) {
		if !slices.Contains(answers, args[1].value()) {
			answers = append(answers, args[1].value())
		}
	}
	if len(answers) != 1 {
		m.problem("the folder conforms with %d answers instead of one", len(answers))
		return broken
	}
	return answers[0]
}

func (m *machine) run() int {
	m.load()
	if len(m.problems) > 0 {
		return m.fail(nil)
	}
	m.prepare()
	m.compile()
	if len(m.problems) > 0 {
		return m.fail(nil)
	}
	if !m.execute() {
		return m.fail(nil)
	}
	store, err := m.evaluate(true)
	if err != nil {
		m.problem("mangle cannot evaluate the knowledge: %v", err)
		return m.fail(nil)
	}
	k := &knowledge{m, store}
	answer := m.answer(k)
	views := k.values("prints", thisFile)
	for _, view := range views {
		m.explain(k, view)
	}
	for _, view := range views {
		m.print(k, view)
	}
	if len(m.problems) > 0 {
		return m.fail(k)
	}
	for _, view := range views {
		m.publish(k, view, answer)
	}
	if len(m.problems) > 0 {
		return m.fail(k)
	}
	os.Stdout.WriteString(m.out.String())
	return m.exitCode(k, answer)
}

func (m *machine) publish(k *knowledge, view, answer string) {
	if when := k.values("is_published_only_when", view); len(when) > 0 && !slices.Contains(when, answer) {
		return
	}
	for _, store := range k.values("is_published_to", view) {
		paths := k.values("is_the_sqlite_file", store)
		if len(paths) != 1 {
			m.problem("%s is not one sqlite file", store)
			continue
		}
		if err := m.write(k, store, paths[0], answer); err != nil {
			m.problem("%s cannot publish %s to %s: %v", thisFile, view, store, err)
		}
	}
}

type row []any

func (m *machine) tables(k *knowledge, store, answer string) (map[string][]string, map[string][]row, error) {
	schema := map[string][]string{}
	rows := map[string][]row{}
	for _, kind := range k.values("keeps", store) {
		switch kind {
		case "every rule with its id":
			schema["rules"] = []string{"name TEXT PRIMARY KEY", "id TEXT NOT NULL", "text TEXT NOT NULL"}
			inView := map[string]bool{}
			for _, args := range k.facts("in_the_knowledge_view", 1) {
				inView[args[0].value()] = true
			}
			for _, r := range m.rules {
				if inView[r.name()] {
					rows["rules"] = append(rows["rules"], row{r.name(), r.id(), strings.Join(r.lines, "\n")})
				}
			}
		case "every fact with its id":
			schema["facts"] = []string{"id TEXT PRIMARY KEY", "fact TEXT NOT NULL"}
			for _, text := range m.allFacts(k) {
				rows["facts"] = append(rows["facts"], row{shortHash(text), text})
			}
		case "every reason for every derived fact":
			schema["reasons"] = []string{"fact_id TEXT NOT NULL", "fact TEXT NOT NULL", "derivation INTEGER NOT NULL", "rule TEXT NOT NULL", "position INTEGER NOT NULL", "reason TEXT NOT NULL"}
			m.eachDerivation(func(text string, n int, d derivation) {
				for i, reason := range d.reasons {
					rows["reasons"] = append(rows["reasons"], row{shortHash(text), text, n, d.rule.name(), i + 1, reason})
				}
			})
		case "every not condition a derived fact rests on":
			schema["not_conditions"] = []string{"fact_id TEXT NOT NULL", "fact TEXT NOT NULL", "derivation INTEGER NOT NULL", "rule TEXT NOT NULL", "condition TEXT NOT NULL"}
			m.eachDerivation(func(text string, n int, d derivation) {
				for i, reason := range d.reasons {
					if d.negated[i] {
						rows["not_conditions"] = append(rows["not_conditions"], row{shortHash(text), text, n, d.rule.name(), reason})
					}
				}
			})
		default:
			parts := k.values("holds", kind)
			if len(parts) == 0 {
				return nil, nil, fmt.Errorf("%s cannot keep %s", store, kind)
			}
			schema["certificate"] = []string{"part TEXT NOT NULL", "subject TEXT NOT NULL", "value TEXT NOT NULL"}
			for _, part := range parts {
				switch part {
				case "the hash of every file engine.go loads":
					for _, file := range m.loaded {
						rows["certificate"] = append(rows["certificate"], row{part, file, m.hashes[file]})
					}
				case "the answer":
					rows["certificate"] = append(rows["certificate"], row{part, "the folder", answer})
				default:
					return nil, nil, fmt.Errorf("%s cannot hold %s", kind, part)
				}
			}
		}
	}
	return schema, rows, nil
}

func (m *machine) eachDerivation(fn func(text string, n int, d derivation)) {
	texts := make([]string, 0, len(m.derived))
	for text := range m.derived {
		texts = append(texts, text)
	}
	sort.Strings(texts)
	for _, text := range texts {
		for n, d := range m.derived[text] {
			fn(text, n+1, d)
		}
	}
}

func (m *machine) allFacts(k *knowledge) []string {
	seen := map[string]bool{}
	var out []string
	for _, sym := range k.store.ListPredicates() {
		k.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			text := m.fromMangle(a).plain()
			if !seen[text] {
				seen[text] = true
				out = append(out, text)
			}
			return nil
		})
	}
	for _, a := range m.extra {
		if text := a.plain(); !seen[text] {
			seen[text] = true
			out = append(out, text)
		}
	}
	sort.Strings(out)
	return out
}

func (m *machine) write(k *knowledge, store, path, answer string) error {
	schema, rows, err := m.tables(k, store, answer)
	if err != nil {
		return err
	}
	fresh := path + ".new"
	os.Remove(fresh)
	db, err := sql.Open("sqlite", fresh)
	if err != nil {
		return err
	}
	defer db.Close()
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	names := make([]string, 0, len(schema))
	for name := range schema {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		columns := schema[name]
		if _, err := tx.Exec("CREATE TABLE " + name + " (" + strings.Join(columns, ", ") + ")"); err != nil {
			tx.Rollback()
			return err
		}
		marks := strings.TrimSuffix(strings.Repeat("?, ", len(columns)), ", ")
		insert, err := tx.Prepare("INSERT OR IGNORE INTO " + name + " VALUES (" + marks + ")")
		if err != nil {
			tx.Rollback()
			return err
		}
		for _, r := range rows[name] {
			if _, err := insert.Exec(r...); err != nil {
				insert.Close()
				tx.Rollback()
				return err
			}
		}
		insert.Close()
	}
	if err := tx.Commit(); err != nil {
		return err
	}
	if err := db.Close(); err != nil {
		return err
	}
	return os.Rename(fresh, path)
}

func main() {
	os.Exit(newMachine().run())
}
