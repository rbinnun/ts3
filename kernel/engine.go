package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	mangle "codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
	_ "modernc.org/sqlite"
)

const (
	engineFile   = "engine.go"
	firstFile    = "spec.plain"
	plainKind    = "rules and facts"
	rowsKind     = "a row per line with a cell per column"
	wayPrefix    = "engine_way_"
	brokenAnswer = "broken"
	factPattern  = "fact pattern"
	problemFact  = "[text] is a problem"
	becauseFact  = "[fact] holds because [reason]"
)

var engineInstructions = []string{
	"[go file] loads [file]",
	"[language] is loaded as [kind]",
	"[line] means in mangle [mangle]",
	"[command] calls [tool] [input]",
	"[answer] exits with [code]",
	"[folder] conforms [answer]",
	"[text] is a problem",
	"[go file] prints [knowledge]",
	"[go file] prints in [language]",
	"[go file] prints to [place]",
	"[rule] is in the knowledge",
	"[knowledge] shows [fact pattern]",
	"[knowledge] gives reasons for [fact pattern]",
	"[knowledge] is published to [store]",
	"[knowledge] is published only when [answer]",
	"[store] is the sqlite file [path]",
	"[store] has the table [table]",
	"[table] has a row for [kind]",
	"[table] has the column [position] [column] [meaning]",
	"[certificate] holds [part]",
	"[kind] is computed as [method]",
	"[file] creates fact [fact pattern]",
}

var computations = map[string]string{
	"a rule id":       "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":       "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a derivation id": "the first 16 hex digits of the sha256 of the fact and the rule name and the reasons as plain lines joined by newlines",
	"a row name":      "the file name and a colon and the line number",
	"a cell value":    "the cell text read as a plain value",
}

var meanings = map[string][]string{
	"every rule":                       {"the rule id", "the rule name", "the file the rule is in", "the number of the line the rule starts on", "the rule lines joined by newlines"},
	"every fact":                       {"the fact id", "the fact as one plain line", "the file that creates the predicate of the fact"},
	"every way a rule derives a fact":  {"the derivation id", "the fact id", "the rule name"},
	"every reason of every derivation": {"the derivation id", "the number of the condition in the rule", "the condition with its blanks filled as one plain line"},
	"every part the certificate holds": {"what the certificate holds", "the file a hash is of and empty for the answer", "the sha256 of the file in hex or the answer"},
}

const (
	hashesPart = "the hash of every file engine.go loads"
	answerPart = "the answer"
)

var keywords = map[string]bool{"do": true, "let": true, "bound": true, "now": true, "opt": true, "descr": true, "inclusion": true, "temporal": true}

var blankForm = regexp.MustCompile(`^\[([^\[\]]+)\]$`)
var numberForm = regexp.MustCompile(`^(0|-?[1-9][0-9]*)$`)

type kind int

const (
	blankTerm kind = iota
	textTerm
	numberTerm
)

type term struct {
	kind kind
	text string
	num  int64
}

func blank(s string) term  { return term{kind: blankTerm, text: s} }
func text(s string) term   { return term{kind: textTerm, text: s} }
func number(n int64) term  { return term{kind: numberTerm, num: n} }
func (t term) raw() string {
	if t.kind == numberTerm {
		return strconv.FormatInt(t.num, 10)
	}
	return t.text
}

type shape int

const (
	sentence shape = iota
	quality
	relation
)

type pred struct {
	shape shape
	name  string
	arity int
}

type atom struct {
	pred pred
	args []term
}

type cond struct {
	negated bool
	atom    atom
}

type rule struct {
	file  string
	order int
	line  int
	text  string
	head  atom
	conds []cond
}

type cell struct {
	column string
	value  term
}

type row struct {
	name   string
	source string
	line   int
	cells  []cell
}

type template struct {
	line atom
	code string
}

type way struct {
	rule    *rule
	fact    atom
	reasons []string
}

type machine struct {
	folder   string
	change   string
	isChange bool
	order    []string
	loaded   map[string]bool
	hashes   map[string]string
	rules    []*rule
	rows     []row
	problems []string
	noted    map[string]bool
	patterns map[string]atom
	first    map[string]int
	shapes   map[string]pred
	tpls     []template
	static   []atom
	returned []atom
	because  []atom
	info     *analysis.ProgramInfo
	vars     map[int][]string
	done     map[string]bool
	cache    map[string][]result
	ways     []way
}

type view struct {
	m     *machine
	store factstore.SimpleInMemoryStore
}

func main() {
	dir, err := os.Getwd()
	if err != nil {
		fmt.Println(quote("engine.go cannot find the folder") + ", is, a problem")
		os.Exit(2)
	}
	m := &machine{
		folder:   dir,
		loaded:   map[string]bool{},
		hashes:   map[string]string{},
		noted:    map[string]bool{},
		patterns: map[string]atom{},
		first:    map[string]int{},
		shapes:   map[string]pred{},
		done:     map[string]bool{},
		cache:    map[string][]result{},
	}
	if len(os.Args) > 1 {
		m.change = os.Args[1]
		m.isChange = true
	}
	os.Exit(m.run())
}

func (m *machine) run() int {
	m.load(firstFile, plainKind)
	m.loadAll()
	m.findPatterns()
	m.findTemplates()
	m.static = m.produce()
	if len(m.problems) > 0 {
		return m.stop(nil)
	}
	if err := m.compile(); err != nil {
		m.problem("engine.go cannot read the knowledge in mangle: " + oneLine(err.Error()))
		return m.stop(nil)
	}
	var k *view
	for round := 0; ; round++ {
		if round > 50 {
			m.problem("the knowledge does not settle")
			return m.stop(k)
		}
		next, err := m.evaluate()
		if err != nil {
			m.problem("engine.go cannot evaluate the knowledge: " + oneLine(err.Error()))
			return m.stop(k)
		}
		k = next
		m.ways = m.findWays(k)
		ran := m.work(k)
		because := m.explain(k)
		if !ran && sameAtoms(because, m.because) {
			break
		}
		m.because = because
	}
	return m.finish(k)
}

func oneLine(s string) string {
	return strings.Join(strings.Fields(s), " ")
}

func (m *machine) problem(s string) {
	if m.noted[s] {
		return
	}
	m.noted[s] = true
	m.problems = append(m.problems, s)
}

func sha16(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])[:16]
}

func splitLine(line string) ([]string, []bool, error) {
	var parts []string
	var quoted []bool
	rest := line
	for {
		if rest != "" && (rest[0] == '"' || rest[0] == '\'') {
			q := rest[0]
			end := strings.IndexByte(rest[1:], q)
			if end < 0 {
				return nil, nil, fmt.Errorf("a quote that is never closed")
			}
			parts = append(parts, rest[1:1+end])
			quoted = append(quoted, true)
			rest = rest[2+end:]
			if rest == "" {
				return parts, quoted, nil
			}
			if !strings.HasPrefix(rest, ", ") {
				return nil, nil, fmt.Errorf("text after a closing quote")
			}
			rest = rest[2:]
			continue
		}
		i := strings.Index(rest, ", ")
		if i < 0 {
			return append(parts, rest), append(quoted, false), nil
		}
		parts = append(parts, rest[:i])
		quoted = append(quoted, false)
		rest = rest[i+2:]
	}
}

func readTerm(s string, quoted bool) term {
	if quoted {
		return text(s)
	}
	if m := blankForm.FindStringSubmatch(s); m != nil {
		return blank(m[1])
	}
	if numberForm.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return number(n)
		}
	}
	return text(s)
}

func readAtom(line string) (atom, error) {
	parts, quoted, err := splitLine(line)
	if err != nil {
		return atom{}, err
	}
	if len(parts) == 1 {
		t := readTerm(parts[0], quoted[0])
		if t.kind == blankTerm || t.raw() == "" {
			return atom{}, fmt.Errorf("a sentence without words")
		}
		return atom{pred: pred{sentence, t.raw(), 0}}, nil
	}
	if len(parts) == 2 {
		return atom{}, fmt.Errorf("a subject and a verb without an object")
	}
	verb := readTerm(parts[1], quoted[1])
	if verb.kind == blankTerm || verb.raw() == "" {
		return atom{}, fmt.Errorf("a verb that is a blank")
	}
	args := []term{readTerm(parts[0], quoted[0])}
	for i := 2; i < len(parts); i++ {
		args = append(args, readTerm(parts[i], quoted[i]))
	}
	if verb.raw() == "is" && len(args) == 2 && args[1].kind == textTerm {
		return atom{pred: pred{quality, args[1].text, 1}, args: args[:1]}, nil
	}
	return atom{pred: pred{relation, verb.raw(), len(args)}, args: args}, nil
}

func needsQuotes(s string) bool {
	return s == "" || strings.Contains(s, ", ") || strings.TrimSpace(s) != s || s[0] == '"' || s[0] == '\'' ||
		blankForm.MatchString(s) || numberForm.MatchString(s) || strings.HasPrefix(s, "not ")
}

func quote(s string) string {
	if !needsQuotes(s) {
		return s
	}
	if strings.Contains(s, `"`) {
		return "'" + s + "'"
	}
	return `"` + s + `"`
}

func (t term) plain() string {
	switch t.kind {
	case blankTerm:
		return "[" + t.text + "]"
	case numberTerm:
		return t.raw()
	}
	return quote(t.text)
}

func (a atom) plain() string {
	switch a.pred.shape {
	case sentence:
		return quote(a.pred.name)
	case quality:
		return a.args[0].plain() + ", is, " + quote(a.pred.name)
	}
	parts := []string{a.args[0].plain(), quote(a.pred.name)}
	for _, t := range a.args[1:] {
		parts = append(parts, t.plain())
	}
	return strings.Join(parts, ", ")
}

func (c cond) plain() string {
	if c.negated {
		return "not " + c.atom.plain()
	}
	return c.atom.plain()
}

func (r *rule) name() string {
	return fmt.Sprintf("%s:%d", r.file, r.line)
}

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

func (r *rule) atoms() []atom {
	out := []atom{r.head}
	for _, c := range r.conds {
		out = append(out, c.atom)
	}
	return out
}

func (r *rule) blanks() []string {
	var out []string
	seen := map[string]bool{}
	for _, a := range r.atoms() {
		for _, t := range a.args {
			if t.kind == blankTerm && !seen[t.text] {
				seen[t.text] = true
				out = append(out, t.text)
			}
		}
	}
	return out
}

func readPattern(s string) (atom, error) {
	var tokens []term
	rest := s
	for rest != "" {
		if rest[0] == '[' {
			end := strings.IndexByte(rest, ']')
			if end < 0 || strings.ContainsRune(rest[1:end], '[') || end == 1 {
				return atom{}, fmt.Errorf("a broken blank")
			}
			tokens = append(tokens, blank(rest[1:end]))
			rest = rest[end+1:]
			continue
		}
		end := strings.IndexByte(rest, '[')
		if end < 0 {
			end = len(rest)
		}
		if w := strings.TrimSpace(rest[:end]); w != "" {
			tokens = append(tokens, text(w))
		}
		rest = rest[end:]
	}
	var a atom
	switch {
	case len(tokens) == 1 && tokens[0].kind == textTerm:
		a = atom{pred: pred{sentence, tokens[0].text, 0}}
	case len(tokens) == 2 && tokens[0].kind == blankTerm && tokens[1].kind == textTerm && strings.HasPrefix(tokens[1].text, "is "):
		a = atom{pred: pred{quality, tokens[1].text[3:], 1}, args: tokens[:1]}
	case len(tokens) >= 3 && tokens[0].kind == blankTerm && tokens[1].kind == textTerm:
		args := []term{tokens[0]}
		for _, t := range tokens[2:] {
			if t.kind != blankTerm {
				return atom{}, fmt.Errorf("words after the blanks")
			}
			args = append(args, t)
		}
		a = atom{pred: pred{relation, tokens[1].text, len(args)}, args: args}
	default:
		return atom{}, fmt.Errorf("no subject and verb")
	}
	if patternText(a) != s {
		return atom{}, fmt.Errorf("not written the way engine.go writes it")
	}
	return a, nil
}

func patternText(a atom) string {
	switch a.pred.shape {
	case sentence:
		return a.pred.name
	case quality:
		return a.args[0].plain() + " is " + a.pred.name
	}
	parts := []string{a.args[0].plain(), a.pred.name}
	for _, t := range a.args[1:] {
		parts = append(parts, t.plain())
	}
	return strings.Join(parts, " ")
}

func (p pred) id() string {
	return fmt.Sprintf("%d|%s|%d", p.shape, p.name, p.arity)
}

func (p pred) mangle() string {
	var b strings.Builder
	gap := false
	for _, r := range strings.ToLower(p.name) {
		if (r >= 'a' && r <= 'z') || (r >= '0' && r <= '9') {
			if gap && b.Len() > 0 {
				b.WriteByte('_')
			}
			gap = false
			b.WriteRune(r)
			continue
		}
		gap = true
	}
	s := b.String()
	if s == "" || s[0] < 'a' || s[0] > 'z' {
		s = "p_" + s
	}
	if keywords[s] {
		s += "_"
	}
	return s
}

func (p pred) sym() ast.PredicateSym {
	return ast.PredicateSym{Symbol: p.mangle(), Arity: p.arity}
}

func symKey(s ast.PredicateSym) string {
	return fmt.Sprintf("%s/%d", s.Symbol, s.Arity)
}

func varName(name string) string {
	var b strings.Builder
	up := true
	for _, r := range name {
		if (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9') {
			if up && r >= 'a' && r <= 'z' {
				r -= 'a' - 'A'
			}
			b.WriteRune(r)
			up = false
			continue
		}
		up = true
	}
	s := b.String()
	if s == "" || s[0] < 'A' || s[0] > 'Z' {
		s = "V" + s
	}
	return s
}

func mangleString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '\\':
			b.WriteString(`\\`)
		case '"':
			b.WriteString(`\"`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func (t term) mangle() string {
	switch t.kind {
	case blankTerm:
		return varName(t.text)
	case numberTerm:
		return t.raw()
	}
	return mangleString(t.text)
}

func (a atom) mangle() string {
	args := make([]string, len(a.args))
	for i, t := range a.args {
		args[i] = t.mangle()
	}
	return a.pred.mangle() + "(" + strings.Join(args, ", ") + ")"
}

func (t term) constant() ast.Constant {
	if t.kind == numberTerm {
		return ast.Number(t.num)
	}
	return ast.String(t.text)
}

func (a atom) ground() ast.Atom {
	args := make([]ast.BaseTerm, len(a.args))
	for i, t := range a.args {
		args[i] = t.constant()
	}
	return ast.NewAtom(a.pred.mangle(), args...)
}

func fromMangle(x ast.BaseTerm) term {
	c, ok := x.(ast.Constant)
	if !ok {
		return text(x.String())
	}
	switch c.Type {
	case ast.StringType:
		return text(c.Symbol)
	case ast.NumberType:
		return number(c.NumValue)
	}
	return text(c.String())
}

func (a atom) fill(bind map[string]term) atom {
	args := make([]term, len(a.args))
	for i, t := range a.args {
		args[i] = t
		if t.kind == blankTerm {
			if v, ok := bind[t.text]; ok {
				args[i] = v
			}
		}
	}
	return atom{a.pred, args}
}

func (m *machine) see(a atom) {
	m.shape(a.pred)
	for _, t := range a.args {
		if t.kind == textTerm {
			if _, ok := m.first[t.text]; !ok {
				m.first[t.text] = len(m.first)
			}
		}
	}
}

func (m *machine) shape(p pred) {
	key := symKey(p.sym())
	if old, ok := m.shapes[key]; ok && old.id() != p.id() {
		m.problem(fmt.Sprintf("%s and %s are one predicate in mangle", quote(old.name), quote(p.name)))
		return
	}
	m.shapes[key] = p
}

func (m *machine) ground(p pred) [][]term {
	var out [][]term
	for _, r := range m.rules {
		if len(r.conds) > 0 || r.head.pred.id() != p.id() {
			continue
		}
		ok := true
		for _, t := range r.head.args {
			if t.kind == blankTerm {
				ok = false
			}
		}
		if ok {
			out = append(out, r.head.args)
		}
	}
	return out
}

func (m *machine) declares(owner, verb, pattern string) bool {
	for _, f := range m.ground(pred{relation, verb, 2}) {
		if f[0] == text(owner) && f[1] == text(pattern) {
			return true
		}
	}
	return false
}

func (m *machine) instruction(owner, pattern string) (pred, bool) {
	if !m.declares(owner, "executes instruction", pattern) {
		return pred{}, false
	}
	a, err := readPattern(pattern)
	if err != nil {
		return pred{}, false
	}
	return a.pred, true
}

func (m *machine) creates(owner, pattern string) (pred, bool) {
	if !m.declares(owner, "creates fact", pattern) {
		return pred{}, false
	}
	a, err := readPattern(pattern)
	if err != nil {
		return pred{}, false
	}
	return a.pred, true
}

func (m *machine) load(name, kind string) {
	if m.loaded[name] {
		return
	}
	m.loaded[name] = true
	data, err := os.ReadFile(filepath.Join(m.folder, name))
	if err != nil {
		return
	}
	sum := sha256.Sum256(data)
	m.hashes[name] = hex.EncodeToString(sum[:])
	m.order = append(m.order, name)
	switch kind {
	case plainKind:
		m.readPlain(name, string(data))
	case rowsKind:
		m.readRows(name, data)
	default:
		m.problem(fmt.Sprintf("engine.go cannot load %s", name))
	}
}

func (m *machine) loadAll() {
	loads, ok := m.instruction(engineFile, "[go file] loads [file]")
	if !ok {
		return
	}
	for {
		before := len(m.loaded)
		for _, f := range m.ground(loads) {
			if f[0] != text(engineFile) || f[1].kind != textTerm || m.loaded[f[1].text] {
				continue
			}
			m.load(f[1].text, m.kindOf(f[1].text))
		}
		if len(m.loaded) == before {
			break
		}
	}
	if k := m.kindOf(firstFile); k != plainKind {
		m.problem(fmt.Sprintf("%s is not loaded as %s", firstFile, plainKind))
	}
}

func (m *machine) kindOf(name string) string {
	ending, language := "", ""
	for _, f := range m.ground(pred{relation, "means", 2}) {
		if f[0].kind == textTerm && f[1].kind == textTerm && strings.HasSuffix(name, f[0].text) && len(f[0].text) > len(ending) {
			ending, language = f[0].text, f[1].text
		}
	}
	loadedAs, ok := m.instruction(engineFile, "[language] is loaded as [kind]")
	if language == "" || !ok {
		return ""
	}
	for _, f := range m.ground(loadedAs) {
		if f[0] == text(language) && f[1].kind == textTerm {
			return f[1].text
		}
	}
	return ""
}

func (m *machine) readPlain(name, content string) {
	lines := strings.Split(content, "\n")
	if n := len(lines); n > 0 && lines[n-1] == "" {
		lines = lines[:n-1]
	}
	var cur *rule
	var raw []string
	broken := false
	flush := func() {
		if cur != nil {
			cur.text = strings.Join(raw, "\n")
			m.rules = append(m.rules, cur)
		}
		cur, raw, broken = nil, nil, false
	}
	for i, line := range lines {
		where := fmt.Sprintf("%s:%d", name, i+1)
		if strings.TrimSpace(line) == "" {
			flush()
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			if broken {
				continue
			}
			if cur == nil {
				m.problem(where + " is a condition without a rule")
				broken = true
				continue
			}
			rest := strings.TrimLeft(line, " \t")
			switch {
			case strings.HasPrefix(rest, "if "):
				rest = rest[3:]
			case strings.HasPrefix(rest, "and "):
				rest = rest[4:]
			default:
				m.problem(where + " is neither a rule nor a condition")
				cur, broken = nil, true
				continue
			}
			negated := false
			if strings.HasPrefix(rest, "not ") {
				negated, rest = true, rest[4:]
			}
			a, err := readAtom(rest)
			if err != nil {
				m.problem(where + " cannot be read: " + err.Error())
				cur, broken = nil, true
				continue
			}
			m.see(a)
			cur.conds = append(cur.conds, cond{negated, a})
			raw = append(raw, line)
			continue
		}
		flush()
		a, err := readAtom(line)
		if err != nil {
			m.problem(where + " cannot be read: " + err.Error())
			broken = true
			continue
		}
		m.see(a)
		cur = &rule{file: name, order: len(m.order) - 1, line: i + 1, head: a}
		raw = []string{line}
	}
	flush()
}

func cellValue(s string) term {
	if len(s) >= 2 && (s[0] == '"' || s[0] == '\'') && s[len(s)-1] == s[0] {
		return text(s[1 : len(s)-1])
	}
	if numberForm.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return number(n)
		}
	}
	return text(s)
}

func (m *machine) readRows(name string, data []byte) {
	r := csv.NewReader(bytes.NewReader(data))
	header, err := r.Read()
	if err != nil {
		m.problem(fmt.Sprintf("%s has no columns", name))
		return
	}
	for {
		rec, err := r.Read()
		if err == io.EOF {
			return
		}
		if err != nil {
			m.problem(fmt.Sprintf("%s cannot be read: %s", name, oneLine(err.Error())))
			return
		}
		line, _ := r.FieldPos(0)
		x := row{name: fmt.Sprintf("%s:%d", name, line), source: name, line: line}
		for i, c := range header {
			x.cells = append(x.cells, cell{c, cellValue(rec[i])})
		}
		m.rows = append(m.rows, x)
	}
}

func baseSlot(name string) string {
	for _, p := range []string{"any ", "other "} {
		if strings.HasPrefix(name, p) {
			return name[len(p):]
		}
	}
	return name
}

func (m *machine) findPatterns() {
	places := map[string]map[int]bool{}
	mark := func(p pred, i int) bool {
		if places[p.id()] == nil {
			places[p.id()] = map[int]bool{}
		}
		if places[p.id()][i] {
			return false
		}
		places[p.id()][i] = true
		return true
	}
	for _, r := range m.rules {
		for _, a := range r.atoms() {
			for i, t := range a.args {
				if t.kind == blankTerm && baseSlot(t.text) == factPattern {
					mark(a.pred, i)
				}
			}
		}
	}
	bad := map[string]bool{}
	for changed := true; changed; {
		changed = false
		for _, r := range m.rules {
			for _, a := range r.atoms() {
				for i, t := range a.args {
					if t.kind != textTerm || !places[a.pred.id()][i] || bad[t.text] {
						continue
					}
					if _, ok := m.patterns[t.text]; ok {
						continue
					}
					pa, err := readPattern(t.text)
					if err != nil {
						bad[t.text] = true
						m.problem(fmt.Sprintf("%s cannot be read as a fact pattern: %s", quote(t.text), err.Error()))
						continue
					}
					m.patterns[t.text] = pa
					m.shape(pa.pred)
					changed = true
					for j, u := range pa.args {
						if baseSlot(u.text) == factPattern {
							mark(pa.pred, j)
						}
					}
				}
			}
		}
	}
}

func (m *machine) defined() map[string]bool {
	out := map[string]bool{}
	for _, r := range m.rules {
		out[r.head.pred.id()] = true
	}
	for _, f := range m.ground(pred{relation, "creates fact", 2}) {
		if pa, ok := m.patterns[f[1].raw()]; ok {
			out[pa.pred.id()] = true
		}
	}
	return out
}

func (m *machine) findTemplates() {
	means, ok := m.instruction(engineFile, "[line] means in mangle [mangle]")
	if !ok {
		return
	}
	defined := m.defined()
	for _, f := range m.ground(means) {
		if f[0].kind != textTerm || f[1].kind != textTerm {
			m.problem(fmt.Sprintf("%s means in mangle %s but is not text", f[0].plain(), f[1].plain()))
			continue
		}
		a, err := readAtom(f[0].text)
		if err != nil {
			m.problem(fmt.Sprintf("%s cannot be read: %s", quote(f[0].text), err.Error()))
			continue
		}
		code := strings.TrimSpace(f[1].text)
		if defined[a.pred.id()] {
			if got := a.mangle() + "."; got != code {
				m.problem(fmt.Sprintf("%s means in mangle %s but engine.go reads it as %s", f[0].text, code, got))
			}
			continue
		}
		m.tpls = append(m.tpls, template{a, strings.TrimSuffix(code, ".")})
	}
}

func (t template) fits(a atom) (map[string]string, int, bool) {
	if t.line.pred.id() != a.pred.id() {
		return nil, 0, false
	}
	binds := map[string]string{}
	exact := 0
	for i, x := range t.line.args {
		y := a.args[i]
		if x.kind == blankTerm {
			name := varName(x.text)
			if old, ok := binds[name]; ok && old != y.mangle() {
				return nil, 0, false
			}
			binds[name] = y.mangle()
			continue
		}
		if x != y {
			return nil, 0, false
		}
		exact++
	}
	return binds, exact, true
}

func isWordByte(c byte) bool {
	return c == '_' || c == ':' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

func substitute(code string, binds map[string]string) string {
	var b strings.Builder
	for i := 0; i < len(code); {
		c := code[i]
		if c == '"' || c == '\'' || c == '`' {
			j := i + 1
			for j < len(code) && code[j] != c {
				if code[j] == '\\' {
					j++
				}
				j++
			}
			if j < len(code) {
				j++
			}
			if j > len(code) {
				j = len(code)
			}
			b.WriteString(code[i:j])
			i = j
			continue
		}
		if isWordByte(c) {
			j := i
			for j < len(code) && isWordByte(code[j]) {
				j++
			}
			word := code[i:j]
			if v, ok := binds[word]; ok {
				word = v
			}
			b.WriteString(word)
			i = j
			continue
		}
		b.WriteByte(c)
		i++
	}
	return b.String()
}

func (m *machine) condMangle(a atom) (string, bool) {
	best, bestExact := -1, -1
	var bestBinds map[string]string
	for i, t := range m.tpls {
		if binds, exact, ok := t.fits(a); ok && exact > bestExact {
			best, bestExact, bestBinds = i, exact, binds
		}
	}
	if best < 0 {
		return a.mangle(), false
	}
	return substitute(m.tpls[best].code, bestBinds), true
}

func (m *machine) edbPreds() []pred {
	var out []pred
	for _, f := range m.ground(pred{relation, "creates fact", 2}) {
		if pa, ok := m.patterns[f[1].raw()]; ok {
			out = append(out, pa.pred)
		}
	}
	return out
}

func (m *machine) compile() error {
	var b strings.Builder
	defined := map[string]bool{}
	used := map[string]pred{}
	m.vars = map[int][]string{}
	for i, r := range m.rules {
		defined[symKey(r.head.pred.sym())] = true
		head := r.head.mangle()
		if len(r.conds) == 0 {
			fmt.Fprintf(&b, "%s.\n", head)
			continue
		}
		var body []string
		for _, c := range r.conds {
			s, builtin := m.condMangle(c.atom)
			if !builtin {
				used[symKey(c.atom.pred.sym())] = c.atom.pred
			}
			if c.negated {
				s = "!" + s
			}
			body = append(body, s)
		}
		names := r.blanks()
		owner := map[string]string{}
		var vs []string
		for _, n := range names {
			v := varName(n)
			if o, ok := owner[v]; ok && o != n {
				return fmt.Errorf("%s uses [%s] and [%s] as one blank", r.name(), o, n)
			}
			owner[v] = n
			vs = append(vs, v)
		}
		m.vars[i] = names
		fmt.Fprintf(&b, "%s :- %s.\n", head, strings.Join(body, ", "))
		fmt.Fprintf(&b, "%s%d(%s) :- %s.\n", wayPrefix, i, strings.Join(vs, ", "), strings.Join(body, ", "))
	}
	unit, err := parse.Unit(strings.NewReader(b.String()))
	if err != nil {
		return err
	}
	extra := map[ast.PredicateSym]ast.Decl{}
	add := func(p pred) {
		if defined[symKey(p.sym())] {
			return
		}
		args := make([]ast.BaseTerm, p.arity)
		for i := range args {
			args[i] = ast.Variable{Symbol: fmt.Sprintf("X%d", i)}
		}
		if d, err := ast.NewDecl(ast.NewAtom(p.mangle(), args...), nil, nil, nil); err == nil {
			extra[p.sym()] = d
		}
	}
	for _, p := range used {
		add(p)
	}
	for _, p := range m.edbPreds() {
		add(p)
	}
	info, err := analysis.AnalyzeOneUnit(unit, extra)
	if err != nil {
		return err
	}
	m.info = info
	return nil
}

var producers = map[string]func(m *machine) [][]term{
	"this run is a change": func(m *machine) [][]term {
		if m.isChange {
			return [][]term{{}}
		}
		return nil
	},
	"[rule] is read back differently": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			if r.plain() != r.text {
				out = append(out, []term{text(r.name())})
			}
		}
		return out
	},
	"[file] has a rule for [predicate]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			out = append(out, []term{text(r.file), text(r.head.pred.name)})
		}
		return out
	},
	"[rule] defines [predicate]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			out = append(out, []term{text(r.name()), text(r.head.pred.name)})
		}
		return out
	},
	"[rule] refers to [predicate]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			for _, c := range r.conds {
				out = append(out, []term{text(r.name()), text(c.atom.pred.name)})
			}
		}
		return out
	},
	"[rule] lays down [law]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			if r.head.pred.id() == (pred{relation, "breaks", 2}).id() && r.head.args[1].kind != blankTerm {
				out = append(out, []term{text(r.name()), r.head.args[1]})
			}
		}
		return out
	},
	"[fact pattern] names [predicate]": func(m *machine) [][]term {
		var out [][]term
		for p, pa := range m.patterns {
			out = append(out, []term{text(p), text(pa.pred.name)})
		}
		return out
	},
	"[rule] has the blank [blank]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			for _, n := range r.blanks() {
				out = append(out, []term{text(r.name()), text(n)})
			}
		}
		return out
	},
	"[fact pattern] has the slot [slot]": func(m *machine) [][]term {
		var out [][]term
		for p, pa := range m.patterns {
			for _, t := range pa.args {
				out = append(out, []term{text(p), text(t.text)})
			}
		}
		return out
	},
	"[rule] has the id [id]": func(m *machine) [][]term {
		var out [][]term
		for _, r := range m.rules {
			out = append(out, []term{text(r.name()), text(sha16(r.text))})
		}
		return out
	},
	"[row] is a row of [source]": func(m *machine) [][]term {
		var out [][]term
		for _, x := range m.rows {
			out = append(out, []term{text(x.name), text(x.source)})
		}
		return out
	},
	"[row] has the cell [column] [value]": func(m *machine) [][]term {
		var out [][]term
		for _, x := range m.rows {
			for _, c := range x.cells {
				out = append(out, []term{text(x.name), text(c.column), c.value})
			}
		}
		return out
	},
	"[row] is on line [number]": func(m *machine) [][]term {
		var out [][]term
		for _, x := range m.rows {
			out = append(out, []term{text(x.name), number(int64(x.line))})
		}
		return out
	},
}

func (m *machine) produce() []atom {
	var out []atom
	for _, f := range m.ground(pred{relation, "creates fact", 2}) {
		owner, p := f[0].raw(), f[1].raw()
		switch owner {
		case engineFile:
			if p == problemFact || p == becauseFact {
				continue
			}
			gen, ok := producers[p]
			pa, known := m.patterns[p]
			if !ok || !known {
				m.problem(fmt.Sprintf("engine.go cannot create %s", quote(p)))
				continue
			}
			for _, args := range gen(m) {
				out = append(out, atom{pa.pred, args})
			}
		case toolsFile:
			if p != returnedPattern {
				m.problem(fmt.Sprintf("tools.go cannot create %s", quote(p)))
			}
		}
	}
	return out
}

func (m *machine) edb() []atom {
	out := append([]atom{}, m.static...)
	if p, ok := m.creates(engineFile, problemFact); ok {
		for _, s := range m.problems {
			out = append(out, atom{p, []term{text(s)}})
		}
	}
	out = append(out, m.because...)
	return append(out, m.returned...)
}

func (m *machine) evaluate() (*view, error) {
	store := factstore.NewSimpleInMemoryStore()
	for _, a := range m.edb() {
		store.Add(a.ground())
	}
	if err := mangle.EvalProgram(m.info, store); err != nil {
		return nil, err
	}
	return &view{m: m, store: store}, nil
}

func argsKey(args []term) string {
	parts := make([]string, len(args))
	for i, t := range args {
		parts[i] = t.plain()
	}
	return strings.Join(parts, "\x00")
}

func (k *view) facts(p pred) [][]term {
	var out [][]term
	k.store.GetFacts(ast.NewQuery(p.sym()), func(a ast.Atom) error {
		args := make([]term, len(a.Args))
		for i, x := range a.Args {
			args[i] = fromMangle(x)
		}
		out = append(out, args)
		return nil
	})
	sort.Slice(out, func(i, j int) bool { return argsKey(out[i]) < argsKey(out[j]) })
	return out
}

func (k *view) match(pa atom) [][]term {
	var out [][]term
	for _, f := range k.facts(pa.pred) {
		bind := map[string]term{}
		ok := true
		for i, t := range pa.args {
			if t.kind == blankTerm {
				if v, seen := bind[t.text]; seen && v != f[i] {
					ok = false
					break
				}
				bind[t.text] = f[i]
				continue
			}
			if t != f[i] {
				ok = false
				break
			}
		}
		if ok {
			out = append(out, f)
		}
	}
	return out
}

func (m *machine) findWays(k *view) []way {
	var out []way
	for i, r := range m.rules {
		if len(r.conds) == 0 {
			out = append(out, way{rule: r, fact: r.head})
			continue
		}
		names := m.vars[i]
		sym := ast.PredicateSym{Symbol: fmt.Sprintf("%s%d", wayPrefix, i), Arity: len(names)}
		k.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			bind := map[string]term{}
			for j, n := range names {
				bind[n] = fromMangle(a.Args[j])
			}
			w := way{rule: r, fact: r.head.fill(bind)}
			for _, c := range r.conds {
				w.reasons = append(w.reasons, cond{c.negated, c.atom.fill(bind)}.plain())
			}
			out = append(out, w)
			return nil
		})
	}
	return out
}

func (m *machine) knowledge(k *view) (term, bool) {
	prints, ok := m.instruction(engineFile, "[go file] prints [knowledge]")
	if !ok {
		return term{}, false
	}
	for _, f := range k.facts(prints) {
		if f[0] == text(engineFile) {
			return f[1], true
		}
	}
	return term{}, false
}

func (m *machine) explain(k *view) []atom {
	gives, ok := m.instruction(engineFile, "[knowledge] gives reasons for [fact pattern]")
	because, ok2 := m.creates(engineFile, becauseFact)
	knowledge, ok3 := m.knowledge(k)
	if !ok || !ok2 || !ok3 {
		return nil
	}
	byFact := map[string][]way{}
	for _, w := range m.ways {
		line := w.fact.plain()
		byFact[line] = append(byFact[line], w)
	}
	seen := map[string]bool{}
	var out []atom
	for _, f := range k.facts(gives) {
		pa, known := m.patterns[f[1].raw()]
		if f[0] != knowledge || !known {
			continue
		}
		for _, args := range k.match(pa) {
			line := atom{pa.pred, args}.plain()
			for _, w := range byFact[line] {
				for _, r := range w.reasons {
					if key := line + "\n" + r; !seen[key] {
						seen[key] = true
						out = append(out, atom{because, []term{text(line), text(r)}})
					}
				}
			}
		}
	}
	sort.Slice(out, func(i, j int) bool { return argsKey(out[i].args) < argsKey(out[j].args) })
	return out
}

func sameAtoms(a, b []atom) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].plain() != b[i].plain() {
			return false
		}
	}
	return true
}

func (m *machine) position(a atom) (int, int) {
	line := a.plain()
	bestOrder, bestLine := 1<<30, 1<<30
	for _, w := range m.ways {
		if w.fact.plain() != line {
			continue
		}
		if w.rule.order < bestOrder || (w.rule.order == bestOrder && w.rule.line < bestLine) {
			bestOrder, bestLine = w.rule.order, w.rule.line
		}
	}
	return bestOrder, bestLine
}

func (m *machine) validate(k *view) {
	for _, f := range m.ground(pred{relation, "executes instruction", 2}) {
		owner, p := f[0].raw(), f[1].raw()
		var known []string
		switch owner {
		case engineFile:
			known = engineInstructions
		case toolsFile:
			known = toolsInstructions
		default:
			continue
		}
		found := false
		for _, s := range known {
			found = found || s == p
		}
		if !found {
			m.problem(fmt.Sprintf("%s cannot execute %s", owner, quote(p)))
		}
	}
	if p, ok := m.instruction(engineFile, "[kind] is computed as [method]"); ok {
		for _, f := range k.facts(p) {
			if computations[f[0].raw()] != f[1].raw() {
				m.problem(fmt.Sprintf("engine.go cannot compute %s as %s", quote(f[0].raw()), quote(f[1].raw())))
			}
		}
	}
	if p, ok := m.instruction(engineFile, "[go file] prints in [language]"); ok {
		for _, f := range k.facts(p) {
			if f[0] == text(engineFile) && f[1] != text("plain language") {
				m.problem("engine.go cannot print in " + quote(f[1].raw()))
			}
		}
	}
	if p, ok := m.instruction(engineFile, "[go file] prints to [place]"); ok {
		for _, f := range k.facts(p) {
			if f[0] == text(engineFile) && f[1] != text("standard output") {
				m.problem("engine.go cannot print to " + quote(f[1].raw()))
			}
		}
	}
	if p, ok := m.instruction(engineFile, "[table] has a row for [kind]"); ok {
		for _, f := range k.facts(p) {
			if _, known := meanings[f[1].raw()]; !known {
				m.problem(fmt.Sprintf("engine.go cannot make a row for %s", quote(f[1].raw())))
			}
		}
	}
	if p, ok := m.instruction(engineFile, "[certificate] holds [part]"); ok {
		for _, f := range k.facts(p) {
			if f[1] != text(hashesPart) && f[1] != text(answerPart) {
				m.problem(fmt.Sprintf("engine.go cannot certify %s", quote(f[1].raw())))
			}
		}
	}
	rowKinds := map[string]string{}
	if p, ok := m.instruction(engineFile, "[table] has a row for [kind]"); ok {
		for _, f := range k.facts(p) {
			rowKinds[f[0].raw()] = f[1].raw()
		}
	}
	if p, ok := m.instruction(engineFile, "[table] has the column [position] [column] [meaning]"); ok {
		for _, f := range k.facts(p) {
			found := false
			for _, s := range meanings[rowKinds[f[0].raw()]] {
				found = found || s == f[3].raw()
			}
			if !found {
				m.problem(fmt.Sprintf("engine.go cannot fill the column %s of %s", quote(f[2].raw()), quote(f[0].raw())))
			}
		}
	}
	if p, ok := m.instruction(engineFile, "[text] is a problem"); ok {
		for _, f := range k.facts(p) {
			m.problem(f[0].raw())
		}
	}
}

func (m *machine) answer(k *view) (term, int, bool) {
	conforms, ok := m.instruction(engineFile, "[folder] conforms [answer]")
	exits, ok2 := m.instruction(engineFile, "[answer] exits with [code]")
	if !ok || !ok2 {
		m.problem("engine.go cannot find the answer")
		return term{}, 0, false
	}
	answers := map[term]bool{}
	var answer term
	for _, f := range k.facts(conforms) {
		answers[f[1]] = true
		answer = f[1]
	}
	if len(answers) != 1 {
		m.problem("the folder does not conform with exactly one answer")
		return term{}, 0, false
	}
	for _, f := range k.facts(exits) {
		if f[0] == answer && f[1].kind == numberTerm {
			return answer, int(f[1].num), true
		}
	}
	m.problem(fmt.Sprintf("%s exits with no code", answer.plain()))
	return term{}, 0, false
}

func (m *machine) brokenCode(k *view) int {
	if exits, ok := m.instruction(engineFile, "[answer] exits with [code]"); ok {
		var facts [][]term
		if k != nil {
			facts = k.facts(exits)
		} else {
			facts = m.ground(exits)
		}
		for _, f := range facts {
			if f[0] == text(brokenAnswer) && f[1].kind == numberTerm {
				return int(f[1].num)
			}
		}
	}
	return 2
}

func (m *machine) show(k *view) []string {
	shows, ok := m.instruction(engineFile, "[knowledge] shows [fact pattern]")
	knowledge, ok2 := m.knowledge(k)
	if !ok || !ok2 {
		return nil
	}
	var pats []string
	for _, f := range k.facts(shows) {
		if _, known := m.patterns[f[1].raw()]; f[0] == knowledge && known {
			pats = append(pats, f[1].raw())
		}
	}
	sort.SliceStable(pats, func(i, j int) bool {
		a, okA := m.first[pats[i]]
		b, okB := m.first[pats[j]]
		if okA != okB {
			return okA
		}
		if a != b {
			return a < b
		}
		return pats[i] < pats[j]
	})
	seen := map[string]bool{}
	var out []string
	for _, p := range pats {
		pa := m.patterns[p]
		var lines []string
		for _, args := range k.match(pa) {
			if l := (atom{pa.pred, args}).plain(); !seen[l] {
				seen[l] = true
				lines = append(lines, l)
			}
		}
		sort.Strings(lines)
		out = append(out, lines...)
	}
	return out
}

func (m *machine) stop(k *view) int {
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	seen := map[string]bool{}
	if k != nil {
		for _, l := range m.show(k) {
			seen[l] = true
			fmt.Fprintln(w, l)
		}
	}
	for _, s := range m.problems {
		if l := text(s).plain() + ", is, a problem"; !seen[l] {
			fmt.Fprintln(w, l)
		}
	}
	return m.brokenCode(k)
}

func (m *machine) finish(k *view) int {
	m.validate(k)
	answer, code, ok := m.answer(k)
	if !ok || len(m.problems) > 0 {
		return m.stop(k)
	}
	if err := m.publish(k, answer); err != nil {
		m.problem("engine.go cannot publish the knowledge: " + oneLine(err.Error()))
		return m.stop(k)
	}
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for _, l := range m.show(k) {
		fmt.Fprintln(w, l)
	}
	return code
}

func (m *machine) creator(name string) string {
	for _, r := range m.rules {
		if r.head.pred.name == name {
			return r.file
		}
	}
	for _, f := range m.ground(pred{relation, "creates fact", 2}) {
		if pa, ok := m.patterns[f[1].raw()]; ok && pa.pred.name == name {
			return f[0].raw()
		}
	}
	return ""
}

func (m *machine) records(kind string, k *view, answer term, holds [][]term) []map[string]any {
	var out []map[string]any
	switch kind {
	case "every rule":
		p, ok := m.instruction(engineFile, "[rule] is in the knowledge")
		if !ok {
			return nil
		}
		in := map[string]bool{}
		for _, f := range k.facts(p) {
			in[f[0].raw()] = true
		}
		for _, r := range m.rules {
			if in[r.name()] {
				out = append(out, map[string]any{
					"the rule id": sha16(r.text), "the rule name": r.name(), "the file the rule is in": r.file,
					"the number of the line the rule starts on": int64(r.line), "the rule lines joined by newlines": r.text,
				})
			}
		}
	case "every fact":
		var syms []ast.PredicateSym
		for _, s := range k.store.ListPredicates() {
			if !strings.HasPrefix(s.Symbol, wayPrefix) {
				syms = append(syms, s)
			}
		}
		sort.Slice(syms, func(i, j int) bool { return symKey(syms[i]) < symKey(syms[j]) })
		for _, s := range syms {
			p, ok := m.shapes[symKey(s)]
			if !ok {
				continue
			}
			origin := m.creator(p.name)
			for _, args := range k.facts(p) {
				line := atom{p, args}.plain()
				out = append(out, map[string]any{"the fact id": sha16(line), "the fact as one plain line": line, "the file that creates the predicate of the fact": origin})
			}
		}
	case "every way a rule derives a fact", "every reason of every derivation":
		seen := map[string]bool{}
		for _, w := range m.ways {
			line := w.fact.plain()
			id := sha16(strings.Join(append([]string{line, w.rule.name()}, w.reasons...), "\n"))
			if seen[id] {
				continue
			}
			seen[id] = true
			if kind == "every way a rule derives a fact" {
				out = append(out, map[string]any{"the derivation id": id, "the fact id": sha16(line), "the rule name": w.rule.name()})
				continue
			}
			for i, r := range w.reasons {
				out = append(out, map[string]any{"the derivation id": id, "the number of the condition in the rule": int64(i + 1), "the condition with its blanks filled as one plain line": r})
			}
		}
	case "every part the certificate holds":
		for _, f := range holds {
			switch f[1].raw() {
			case hashesPart:
				for _, name := range m.order {
					out = append(out, map[string]any{"what the certificate holds": hashesPart, "the file a hash is of and empty for the answer": name, "the sha256 of the file in hex or the answer": m.hashes[name]})
				}
			case answerPart:
				out = append(out, map[string]any{"what the certificate holds": answerPart, "the file a hash is of and empty for the answer": "", "the sha256 of the file in hex or the answer": answer.raw()})
			}
		}
	}
	return out
}

func sqlName(s string) string {
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func (m *machine) publish(k *view, answer term) error {
	to, ok1 := m.instruction(engineFile, "[knowledge] is published to [store]")
	when, ok2 := m.instruction(engineFile, "[knowledge] is published only when [answer]")
	file, ok3 := m.instruction(engineFile, "[store] is the sqlite file [path]")
	tables, ok4 := m.instruction(engineFile, "[store] has the table [table]")
	rowsFor, ok5 := m.instruction(engineFile, "[table] has a row for [kind]")
	columns, ok6 := m.instruction(engineFile, "[table] has the column [position] [column] [meaning]")
	knowledge, ok7 := m.knowledge(k)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 || !ok7 {
		return nil
	}
	var holds [][]term
	if p, ok := m.instruction(engineFile, "[certificate] holds [part]"); ok {
		holds = k.facts(p)
	}
	for _, f := range k.facts(when) {
		if f[0] == knowledge && f[1] != answer {
			return nil
		}
	}
	for _, f := range k.facts(to) {
		if f[0] != knowledge {
			continue
		}
		store := f[1]
		for _, g := range k.facts(file) {
			if g[0] == store {
				if err := m.write(k, answer, holds, store, filepath.Join(m.folder, g[1].raw()), tables, rowsFor, columns); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func (m *machine) write(k *view, answer term, holds [][]term, store term, path string, tables, rowsFor, columns pred) error {
	tmp := path + ".new"
	os.Remove(tmp)
	db, err := sql.Open("sqlite", tmp)
	if err != nil {
		return err
	}
	defer db.Close()
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	var names []string
	for _, f := range k.facts(tables) {
		if f[0] == store {
			names = append(names, f[1].raw())
		}
	}
	sort.SliceStable(names, func(i, j int) bool { return m.first[names[i]] < m.first[names[j]] })
	for _, table := range names {
		kind := ""
		for _, f := range k.facts(rowsFor) {
			if f[0] == text(table) {
				kind = f[1].raw()
			}
		}
		type column struct {
			at      int64
			name    string
			meaning string
		}
		var cols []column
		for _, f := range k.facts(columns) {
			if f[0] == text(table) {
				cols = append(cols, column{f[1].num, f[2].raw(), f[3].raw()})
			}
		}
		sort.Slice(cols, func(i, j int) bool { return cols[i].at < cols[j].at })
		recs := m.records(kind, k, answer, holds)
		var defs, marks []string
		for _, c := range cols {
			typ := "TEXT"
			if len(recs) > 0 {
				if _, isNum := recs[0][c.meaning].(int64); isNum {
					typ = "INTEGER"
				}
			}
			defs = append(defs, sqlName(c.name)+" "+typ)
			marks = append(marks, "?")
		}
		if _, err := tx.Exec(fmt.Sprintf("CREATE TABLE %s (%s)", sqlName(table), strings.Join(defs, ", "))); err != nil {
			tx.Rollback()
			return err
		}
		stmt, err := tx.Prepare(fmt.Sprintf("INSERT INTO %s VALUES (%s)", sqlName(table), strings.Join(marks, ", ")))
		if err != nil {
			tx.Rollback()
			return err
		}
		for _, r := range recs {
			vals := make([]any, len(cols))
			for i, c := range cols {
				vals[i] = r[c.meaning]
			}
			if _, err := stmt.Exec(vals...); err != nil {
				stmt.Close()
				tx.Rollback()
				return err
			}
		}
		stmt.Close()
	}
	if err := tx.Commit(); err != nil {
		return err
	}
	if err := db.Close(); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}
