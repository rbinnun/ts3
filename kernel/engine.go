package main

import (
	"crypto/sha256"
	"database/sql"
	"encoding/csv"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"

	"github.com/google/mangle/analysis"
	"github.com/google/mangle/ast"
	"github.com/google/mangle/engine"
	"github.com/google/mangle/factstore"
	"github.com/google/mangle/parse"
	_ "modernc.org/sqlite"
)

const (
	kindString = iota
	kindNumber
	kindBlank
)

const (
	engineFile     = "engine.go"
	toolsFile      = "tools.go"
	derivedOrigin  = "derived"
	levelStore     = "the level store"
	partLevel      = "the name of the level being proven"
	partHash       = "the hash of every file engine.go loads or the level is tested with"
	partAnswer     = "the answer"
	changeVariable = "PLAIN_CHANGE"
	auxPrefix      = "derivation__"
)

var (
	phraseRe = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	numberRe = regexp.MustCompile(`^(0|-?[1-9][0-9]*)$`)
	blankRe  = regexp.MustCompile(`^\[([^\[\]]+)\]$`)
	nameRe   = regexp.MustCompile(`^[a-z][a-z0-9_]*$`)
	keywords = map[string]bool{"descr": true, "inclusion": true, "opt": true, "bound": true, "let": true, "do": true}
)

type value struct {
	kind int
	text string
	num  int64
}

type atom struct {
	pred string
	args []value
}

type condition struct {
	negated bool
	atom    atom
}

type rule struct {
	name  string
	file  string
	line  int
	lines []string
	head  atom
	conds []condition
	level string
	bad   bool
	body  string
	index int
}

type loadedFile struct {
	name      string
	path      string
	level     string
	kind      string
	data      []byte
	tested    bool
	certified bool
	rules     []*rule
}

type template struct {
	args      []value
	text      string
	constants int
}

type pattern struct {
	phrase string
	arity  int
	slots  []string
}

type derivation struct {
	fact    string
	atom    ast.Atom
	rule    *rule
	reasons []string
}

type call struct {
	command ast.Constant
	tool    string
	input   string
	key     string
}

type machine struct {
	kernelDir   string
	root        string
	level       string
	folder      string
	change      string
	levels      []string
	files       []*loadedFile
	rules       []*rule
	problems    []string
	proven      map[string]bool
	templates   map[string][]template
	decls       map[string]int
	observed    []ast.Atom
	origins     map[string]string
	toolFacts   []ast.Atom
	ran         map[string]bool
	program     string
	info        *analysis.ProgramInfo
	store       factstore.FactStore
	derivations []derivation
	reasonKeys  map[string]bool
}

func main() {
	os.Exit(run())
}

func run() int {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "engine.go needs the kernel folder")
		return 2
	}
	kernelDir, err := filepath.Abs(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	cwd, err := os.Getwd()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	m := newMachine(kernelDir, cwd)
	m.load()
	if len(m.problems) > 0 {
		return m.fail()
	}
	m.observeRules()
	m.compile()
	if len(m.problems) > 0 {
		return m.fail()
	}
	for {
		if err := m.evaluate(); err != nil {
			m.problem("the rules cannot be evaluated: " + err.Error())
			return m.fail()
		}
		calls := m.pendingCalls()
		if len(calls) == 0 {
			break
		}
		m.runCalls(calls)
	}
	answer := m.answer()
	publish := m.publishedWhen(answer)
	if err := m.derive(publish); err != nil {
		m.problem("the reasons cannot be found: " + err.Error())
		return m.fail()
	}
	m.giveReasons()
	m.print()
	if publish {
		if err := m.publish(answer); err != nil {
			fmt.Fprintln(os.Stderr, "the knowledge cannot be published:", err)
		}
	} else {
		m.unpublish()
	}
	return m.exitCode(answer)
}

func newMachine(kernelDir, cwd string) *machine {
	m := &machine{
		kernelDir:  kernelDir,
		root:       filepath.Dir(kernelDir),
		level:      filepath.Base(cwd),
		change:     os.Getenv(changeVariable),
		proven:     map[string]bool{},
		templates:  map[string][]template{},
		decls:      map[string]int{},
		origins:    map[string]string{},
		ran:        map[string]bool{},
		reasonKeys: map[string]bool{},
	}
	m.folder = filepath.Join(m.root, m.level)
	return m
}

func (m *machine) problem(text string) {
	m.problems = append(m.problems, text)
}

func str(s string) value {
	return value{kind: kindString, text: s}
}

func key(phrase string, arity int) string {
	return phrase + "/" + strconv.Itoa(arity)
}

func (a atom) key() string {
	return key(a.pred, len(a.args))
}

func mangleName(phrase string) string {
	n := strings.ReplaceAll(phrase, " ", "_")
	if keywords[n] {
		n += "_"
	}
	return n
}

func phraseOf(name string) string {
	n := name
	if strings.HasSuffix(n, "_") && keywords[strings.TrimSuffix(n, "_")] {
		n = strings.TrimSuffix(n, "_")
	}
	return strings.ReplaceAll(n, "_", " ")
}

func sha16(s string) string {
	h := sha256.Sum256([]byte(s))
	return hex.EncodeToString(h[:])[:16]
}

func shaHex(data []byte) string {
	h := sha256.Sum256(data)
	return hex.EncodeToString(h[:])
}

func splitParts(line string) ([]string, error) {
	var parts []string
	i := 0
	for {
		if i < len(line) && (line[i] == '"' || line[i] == '\'') {
			q := line[i]
			end := -1
			for j := i + 1; j < len(line); j++ {
				if line[j] == q && (j+1 == len(line) || strings.HasPrefix(line[j+1:], ", ")) {
					end = j
					break
				}
			}
			if end < 0 {
				return nil, errors.New("a quote is never closed")
			}
			parts = append(parts, line[i:end+1])
			i = end + 1
			if i == len(line) {
				return parts, nil
			}
			i += 2
			continue
		}
		k := strings.Index(line[i:], ", ")
		if k < 0 {
			return append(parts, line[i:]), nil
		}
		parts = append(parts, line[i:i+k])
		i += k + 2
	}
}

func parseValue(raw string) value {
	if len(raw) >= 2 && (raw[0] == '"' || raw[0] == '\'') && raw[len(raw)-1] == raw[0] {
		return str(raw[1 : len(raw)-1])
	}
	if numberRe.MatchString(raw) {
		if n, err := strconv.ParseInt(raw, 10, 64); err == nil {
			return value{kind: kindNumber, num: n}
		}
	}
	if sub := blankRe.FindStringSubmatch(raw); sub != nil {
		return value{kind: kindBlank, text: sub[1]}
	}
	return str(raw)
}

func needsQuotes(s string) bool {
	if s == "" || strings.Contains(s, ", ") || strings.ContainsAny(s, "\n\r") {
		return true
	}
	if s[0] == ' ' || s[len(s)-1] == ' ' || s[0] == '"' || s[0] == '\'' {
		return true
	}
	return numberRe.MatchString(s) || blankRe.MatchString(s)
}

func quoteIfNeeded(s string) string {
	if !needsQuotes(s) {
		return s
	}
	switch {
	case !strings.Contains(s, `"`):
		return `"` + s + `"`
	case !strings.Contains(s, "'"):
		return "'" + s + "'"
	case !strings.Contains(s, `", `):
		return `"` + s + `"`
	}
	return "'" + s + "'"
}

func formatValue(v value) string {
	switch v.kind {
	case kindNumber:
		return strconv.FormatInt(v.num, 10)
	case kindBlank:
		return "[" + v.text + "]"
	}
	return quoteIfNeeded(v.text)
}

func parseAtom(text string) (atom, error) {
	parts, err := splitParts(text)
	if err != nil {
		return atom{}, err
	}
	if len(parts) == 1 {
		if !phraseRe.MatchString(parts[0]) {
			return atom{}, errors.New("a sentence must be plain lowercase words")
		}
		return atom{pred: parts[0]}, nil
	}
	if len(parts) == 2 {
		return atom{}, errors.New("a statement needs a subject, a verb and what the verb is about")
	}
	verb := parts[1]
	if !phraseRe.MatchString(verb) {
		return atom{}, errors.New("the verb must be plain lowercase words")
	}
	subject := parseValue(parts[0])
	if verb == "is" {
		if len(parts) != 3 || !phraseRe.MatchString(parts[2]) {
			return atom{}, errors.New("what something is must be plain lowercase words")
		}
		return atom{pred: parts[2], args: []value{subject}}, nil
	}
	args := []value{subject}
	for _, p := range parts[2:] {
		args = append(args, parseValue(p))
	}
	return atom{pred: verb, args: args}, nil
}

func formatAtom(a atom) string {
	switch len(a.args) {
	case 0:
		return a.pred
	case 1:
		return formatValue(a.args[0]) + ", is, " + a.pred
	}
	parts := []string{formatValue(a.args[0]), a.pred}
	for _, v := range a.args[1:] {
		parts = append(parts, formatValue(v))
	}
	return strings.Join(parts, ", ")
}

func parsePattern(s string) (pattern, bool) {
	type item struct {
		blank bool
		text  string
	}
	var items []item
	i := 0
	for i < len(s) {
		c := s[i]
		if c == ' ' {
			i++
			continue
		}
		if c == '[' {
			j := strings.IndexByte(s[i:], ']')
			if j < 0 {
				return pattern{}, false
			}
			name := s[i+1 : i+j]
			if name == "" || strings.Contains(name, "[") {
				return pattern{}, false
			}
			items = append(items, item{blank: true, text: name})
			i += j + 1
			continue
		}
		j := i
		for j < len(s) && s[j] != ' ' && s[j] != '[' {
			j++
		}
		items = append(items, item{text: s[i:j]})
		i = j
	}
	if len(items) == 0 {
		return pattern{}, false
	}
	hasBlank := false
	for _, it := range items {
		hasBlank = hasBlank || it.blank
	}
	if !hasBlank {
		if !phraseRe.MatchString(s) {
			return pattern{}, false
		}
		return pattern{phrase: s}, true
	}
	if !items[0].blank {
		return pattern{}, false
	}
	k := 1
	var verb []string
	for k < len(items) && !items[k].blank {
		verb = append(verb, items[k].text)
		k++
	}
	if len(verb) == 0 {
		return pattern{}, false
	}
	slots := []string{items[0].text}
	for ; k < len(items); k++ {
		if !items[k].blank {
			return pattern{}, false
		}
		slots = append(slots, items[k].text)
	}
	v := strings.Join(verb, " ")
	if !phraseRe.MatchString(v) {
		return pattern{}, false
	}
	if len(slots) == 1 {
		if !strings.HasPrefix(v, "is ") {
			return pattern{}, false
		}
		return pattern{phrase: v[3:], arity: 1, slots: slots}, true
	}
	if v == "is" {
		return pattern{}, false
	}
	return pattern{phrase: v, arity: len(slots), slots: slots}, true
}

func (p pattern) key() string {
	return key(p.phrase, p.arity)
}

func varName(blank string) string {
	var b strings.Builder
	word := true
	for i := 0; i < len(blank); i++ {
		c := blank[i]
		isLetter := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
		isDigit := c >= '0' && c <= '9'
		if !isLetter && !isDigit {
			word = true
			continue
		}
		if word && c >= 'a' && c <= 'z' {
			c = c - 'a' + 'A'
		}
		b.WriteByte(c)
		word = false
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
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '\\':
			b.WriteString(`\\`)
		case c == '"':
			b.WriteString(`\"`)
		case c == '\n':
			b.WriteString(`\n`)
		case c == '\t':
			b.WriteString(`\t`)
		case c < 0x20:
			fmt.Fprintf(&b, `\x%02x`, c)
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func mangleTerm(v value) string {
	switch v.kind {
	case kindNumber:
		return strconv.FormatInt(v.num, 10)
	case kindBlank:
		return varName(v.text)
	}
	return mangleString(v.text)
}

func mangleAtom(a atom) string {
	terms := make([]string, len(a.args))
	for i, v := range a.args {
		terms[i] = mangleTerm(v)
	}
	return mangleName(a.pred) + "(" + strings.Join(terms, ", ") + ")"
}

func sameValue(a, b value) bool {
	return a.kind == b.kind && a.text == b.text && a.num == b.num
}

func isIdentStart(c byte) bool {
	return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func isIdentChar(c byte) bool {
	return isIdentStart(c) || (c >= '0' && c <= '9')
}

func replaceVariables(text string, sub map[string]string) string {
	var b strings.Builder
	i := 0
	for i < len(text) {
		c := text[i]
		if c == '"' || c == '\'' {
			j := i + 1
			for j < len(text) && text[j] != c {
				if text[j] == '\\' {
					j++
				}
				j++
			}
			j++
			if j > len(text) {
				j = len(text)
			}
			b.WriteString(text[i:j])
			i = j
			continue
		}
		if isIdentStart(c) {
			j := i
			for j < len(text) && isIdentChar(text[j]) {
				j++
			}
			word := text[i:j]
			if r, ok := sub[word]; ok && (i == 0 || text[i-1] != ':') {
				b.WriteString(r)
			} else {
				b.WriteString(word)
			}
			i = j
			continue
		}
		b.WriteByte(c)
		i++
	}
	return b.String()
}

func expand(t template, a atom) (string, bool) {
	if len(t.args) != len(a.args) {
		return "", false
	}
	sub := map[string]string{}
	for i, ta := range t.args {
		if ta.kind == kindBlank {
			sub[varName(ta.text)] = mangleTerm(a.args[i])
			continue
		}
		if !sameValue(ta, a.args[i]) {
			return "", false
		}
	}
	return replaceVariables(t.text, sub), true
}

func (m *machine) mangleCondition(c condition) (string, error) {
	if ts, ok := m.templates[c.atom.key()]; ok {
		for _, t := range ts {
			if s, ok := expand(t, c.atom); ok {
				if c.negated {
					return "", fmt.Errorf("%s cannot be negated", c.atom.pred)
				}
				return s, nil
			}
		}
		return "", fmt.Errorf("no meaning in mangle fits %s", formatAtom(c.atom))
	}
	s := mangleAtom(c.atom)
	if c.negated {
		s = "!" + s
	}
	return s, nil
}

func (r *rule) canonical() string {
	var b strings.Builder
	b.WriteString(formatAtom(r.head))
	for i, c := range r.conds {
		if i == 0 {
			b.WriteString("\n    if ")
		} else {
			b.WriteString("\n    and ")
		}
		if c.negated {
			b.WriteString("not ")
		}
		b.WriteString(formatAtom(c.atom))
	}
	return b.String()
}

func (r *rule) text() string {
	return strings.Join(r.lines, "\n")
}

func (r *rule) atoms() []atom {
	out := []atom{r.head}
	for _, c := range r.conds {
		out = append(out, c.atom)
	}
	return out
}

func (r *rule) fact(pred string, arity int) bool {
	return len(r.conds) == 0 && r.head.pred == pred && len(r.head.args) == arity
}

func fileLines(data []byte) []string {
	lines := strings.Split(string(data), "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	return lines
}

func (m *machine) parsePlain(f *loadedFile) {
	var cur *rule
	for i, l := range fileLines(f.data) {
		n := i + 1
		where := fmt.Sprintf("%s:%d", f.name, n)
		if strings.TrimSpace(l) == "" {
			cur = nil
			continue
		}
		isIf := strings.HasPrefix(l, "    if ")
		isAnd := strings.HasPrefix(l, "    and ")
		if isIf || isAnd {
			if cur == nil {
				m.problem(where + " is a condition with no statement before it")
				continue
			}
			if cur.bad {
				continue
			}
			if isIf != (len(cur.conds) == 0) {
				m.problem(where + " must begin with if for the first condition and with and for the others")
				cur.bad = true
				continue
			}
			body := strings.TrimPrefix(l, "    if ")
			if isAnd {
				body = strings.TrimPrefix(l, "    and ")
			}
			negated := strings.HasPrefix(body, "not ")
			if negated {
				body = body[4:]
			}
			a, err := parseAtom(body)
			if err != nil {
				m.problem(fmt.Sprintf("%s cannot be read: %v", where, err))
				cur.bad = true
				continue
			}
			cur.conds = append(cur.conds, condition{negated: negated, atom: a})
			cur.lines = append(cur.lines, l)
			continue
		}
		if l[0] == ' ' || l[0] == '\t' {
			m.problem(where + " is indented but is not a condition")
			cur = &rule{bad: true}
			continue
		}
		a, err := parseAtom(l)
		r := &rule{name: where, file: f.name, line: n, lines: []string{l}, head: a, level: f.level}
		if err != nil {
			m.problem(fmt.Sprintf("%s cannot be read: %v", where, err))
			r.bad = true
		}
		f.rules = append(f.rules, r)
		cur = r
	}
	kept := f.rules[:0]
	for _, r := range f.rules {
		if !r.bad {
			kept = append(kept, r)
		}
	}
	f.rules = kept
}

func (m *machine) readFile(level, name, kind string, tested bool) *loadedFile {
	path := filepath.Join(m.root, level, name)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil
	}
	f := &loadedFile{name: name, path: path, level: level, kind: kind, data: data, tested: tested}
	if kind == "plain" {
		m.parsePlain(f)
	}
	return f
}

func exists(path string) bool {
	st, err := os.Stat(path)
	return err == nil && !st.IsDir()
}

func isDir(path string) bool {
	st, err := os.Stat(path)
	return err == nil && st.IsDir()
}

func (m *machine) load() {
	seen := map[string]bool{m.level: true}
	m.levels = []string{m.level}
	levelFiles := map[string]*loadedFile{}
	for i := 0; i < len(m.levels); i++ {
		l := m.levels[i]
		if !isDir(filepath.Join(m.root, l)) {
			if l == m.level {
				m.problem(fmt.Sprintf("the level %s has no folder next to the kernel folder", l))
			}
			continue
		}
		f := m.readFile(l, l+".plain", "plain", false)
		if f == nil {
			m.problem(fmt.Sprintf("the level %s has no level file %s.plain", l, l))
			continue
		}
		levelFiles[l] = f
		for _, r := range f.rules {
			if r.fact("builds on", 2) && r.head.args[1].kind == kindString {
				o := r.head.args[1].text
				if !seen[o] {
					seen[o] = true
					m.levels = append(m.levels, o)
				}
			}
		}
	}
	endings := map[string]string{}
	loadedAs := map[string]string{}
	privateKeys := map[string]bool{}
	for _, l := range m.levels {
		f := levelFiles[l]
		if f == nil {
			continue
		}
		for _, r := range f.rules {
			if len(r.conds) > 0 {
				continue
			}
			args := r.head.args
			switch {
			case r.fact("means", 2) && args[0].kind == kindString && args[1].kind == kindString:
				endings[args[0].text] = args[1].text
			case r.fact("is loaded as", 2) && args[0].kind == kindString && args[1].kind == kindString:
				loadedAs[args[0].text] = args[1].text
			case r.fact("private to its level", 1) && args[0].kind == kindString:
				if p, ok := parsePattern(args[0].text); ok {
					privateKeys[p.key()] = true
				}
			}
		}
	}
	kindOf := func(name string) (string, bool) {
		best, language := "", ""
		for ending, lang := range endings {
			if strings.HasSuffix(name, ending) && len(ending) > len(best) {
				best, language = ending, lang
			}
		}
		switch loadedAs[language] {
		case "rules and facts":
			return "plain", true
		case "a row per line with a cell per column":
			return "rows", true
		}
		return "", false
	}
	groups := map[string][]*loadedFile{}
	for _, l := range m.levels {
		f := levelFiles[l]
		if f == nil {
			continue
		}
		group := []*loadedFile{f}
		names := map[string]bool{f.name: true}
		add := func(name string, tested bool) {
			if names[name] || !exists(filepath.Join(m.root, l, name)) {
				return
			}
			names[name] = true
			kind, ok := kindOf(name)
			if !ok {
				m.problem(fmt.Sprintf("%s cannot be loaded because nothing says how to load it", name))
				return
			}
			if g := m.readFile(l, name, kind, tested); g != nil {
				group = append(group, g)
			}
		}
		for _, r := range f.rules {
			if r.fact("loads", 2) && r.head.args[0].kind == kindString && r.head.args[0].text == engineFile && r.head.args[1].kind == kindString {
				add(r.head.args[1].text, false)
			}
		}
		if l == m.level {
			for _, r := range f.rules {
				if r.fact("is tested with", 2) && r.head.args[0].kind == kindString && r.head.args[0].text == l && r.head.args[1].kind == kindString {
					add(r.head.args[1].text, true)
				}
			}
		}
		groups[l] = group
	}
	for i := len(m.levels) - 1; i >= 0; i-- {
		m.files = append(m.files, groups[m.levels[i]]...)
	}
	owner := map[string]string{}
	for _, f := range m.files {
		if o, ok := owner[f.name]; ok {
			m.problem(fmt.Sprintf("two loaded files are named %s, in %s and in %s", f.name, o, f.level))
		}
		owner[f.name] = f.level
	}
	if levelFiles[m.level] == nil {
		return
	}
	for _, l := range m.levels[1:] {
		if levelFiles[l] != nil && m.checkProven(l) {
			m.proven[l] = true
		}
	}
	for _, f := range m.files {
		f.certified = m.proven[f.level]
		if f.kind != "plain" {
			continue
		}
		for _, r := range f.rules {
			if f.certified && len(r.conds) == 0 && privateKeys[r.head.key()] {
				continue
			}
			r.index = len(m.rules)
			m.rules = append(m.rules, r)
		}
	}
	for _, f := range m.files {
		if f.kind == "rows" {
			m.loadRows(f)
		}
	}
}

func (m *machine) locate(level, name string) string {
	candidates := []string{filepath.Join(m.root, level, name)}
	for _, l := range m.levels {
		candidates = append(candidates, filepath.Join(m.root, l, name))
	}
	for _, c := range candidates {
		if exists(c) {
			return c
		}
	}
	return ""
}

func (m *machine) checkProven(level string) bool {
	path := filepath.Join(m.root, level+".db")
	if !exists(path) {
		return false
	}
	db, err := sql.Open("sqlite", path)
	if err != nil {
		return false
	}
	defer db.Close()
	rows, err := db.Query(`SELECT part, subject, value FROM certificate`)
	if err != nil {
		return false
	}
	defer rows.Close()
	hasName, hasAnswer, hashes := false, false, 0
	for rows.Next() {
		var part, subject, val sql.NullString
		if err := rows.Scan(&part, &subject, &val); err != nil {
			return false
		}
		switch part.String {
		case partLevel:
			hasName = hasName || val.String == level
		case partAnswer:
			hasAnswer = hasAnswer || val.String == "true"
		case partHash:
			hashes++
			p := m.locate(level, subject.String)
			if p == "" {
				return false
			}
			data, err := os.ReadFile(p)
			if err != nil || shaHex(data) != val.String {
				return false
			}
		}
	}
	return rows.Err() == nil && hasName && hasAnswer && hashes > 0
}

func plainConstant(text string) ast.Constant {
	if numberRe.MatchString(text) {
		if n, err := strconv.ParseInt(text, 10, 64); err == nil {
			return ast.Number(n)
		}
	}
	return ast.String(text)
}

func (m *machine) loadRows(f *loadedFile) {
	lines := fileLines(f.data)
	if len(lines) == 0 {
		return
	}
	readCells := func(l string) ([]string, error) {
		r := csv.NewReader(strings.NewReader(strings.TrimSuffix(l, "\r")))
		r.FieldsPerRecord = -1
		r.LazyQuotes = true
		return r.Read()
	}
	header, err := readCells(lines[0])
	if err != nil {
		m.problem(fmt.Sprintf("%s:1 cannot be read as the names of the columns", f.name))
		return
	}
	for i := 1; i < len(lines); i++ {
		if strings.TrimSpace(lines[i]) == "" {
			continue
		}
		where := fmt.Sprintf("%s:%d", f.name, i+1)
		cells, err := readCells(lines[i])
		if err != nil || len(cells) != len(header) {
			m.problem(where + " does not have one cell for every column")
			continue
		}
		m.observe("is a row of", ast.String(where), ast.String(f.name))
		m.observe("is on line", ast.String(where), ast.Number(int64(i+1)))
		for j, column := range header {
			m.observe("has the cell", ast.String(where), ast.String(column), plainConstant(cells[j]))
		}
	}
}

func newAtom(phrase string, args ...ast.Constant) ast.Atom {
	terms := make([]ast.BaseTerm, len(args))
	for i, a := range args {
		terms[i] = a
	}
	return ast.Atom{Predicate: ast.PredicateSym{Symbol: mangleName(phrase), Arity: len(args)}, Args: terms}
}

func (m *machine) observe(phrase string, args ...ast.Constant) {
	a := newAtom(phrase, args...)
	m.observed = append(m.observed, a)
	m.origins[lineOf(a)] = engineFile
}

func valueOf(c ast.Constant) value {
	switch c.Type {
	case ast.NumberType:
		n, _ := c.NumberValue()
		return value{kind: kindNumber, num: n}
	case ast.StringType:
		s, _ := c.StringValue()
		return str(s)
	}
	return str(c.String())
}

func constOf(v value) ast.Constant {
	if v.kind == kindNumber {
		return ast.Number(v.num)
	}
	return ast.String(v.text)
}

func textOf(c ast.Constant) string {
	v := valueOf(c)
	if v.kind == kindNumber {
		return strconv.FormatInt(v.num, 10)
	}
	return v.text
}

func constants(a ast.Atom) []ast.Constant {
	out := make([]ast.Constant, len(a.Args))
	for i, t := range a.Args {
		out[i], _ = t.(ast.Constant)
	}
	return out
}

func atomOf(a ast.Atom) atom {
	cs := constants(a)
	args := make([]value, len(cs))
	for i, c := range cs {
		args[i] = valueOf(c)
	}
	return atom{pred: phraseOf(a.Predicate.Symbol), args: args}
}

func lineOf(a ast.Atom) string {
	return formatAtom(atomOf(a))
}

func symKey(sym ast.PredicateSym) string {
	return key(phraseOf(sym.Symbol), sym.Arity)
}

func (m *machine) observeRules() {
	if m.change != "" {
		m.observe("this run is a change")
	}
	for _, l := range m.levels {
		if m.proven[l] {
			m.observe("proven", ast.String(l))
		}
	}
	for _, f := range m.files {
		if f.certified {
			m.observe("certified", ast.String(f.name))
		}
	}
	places := map[string]bool{}
	for _, r := range m.rules {
		for _, a := range r.atoms() {
			for i, v := range a.args {
				if v.kind == kindBlank && v.text == "fact pattern" {
					places[a.key()+"#"+strconv.Itoa(i)] = true
				}
			}
		}
	}
	seen := map[string]bool{}
	for _, r := range m.rules {
		for _, a := range r.atoms() {
			for i, v := range a.args {
				if v.kind != kindString || !places[a.key()+"#"+strconv.Itoa(i)] || seen[v.text] {
					continue
				}
				seen[v.text] = true
				p, ok := parsePattern(v.text)
				if !ok {
					continue
				}
				m.observe("names", ast.String(v.text), ast.String(p.phrase))
				for _, s := range p.slots {
					m.observe("has the slot", ast.String(v.text), ast.String(s))
				}
				m.decls[mangleName(p.phrase)] = p.arity
			}
		}
	}
	for _, r := range m.rules {
		name := ast.String(r.name)
		m.observe("has the id", name, ast.String(sha16(r.text())))
		m.observe("is in the file", name, ast.String(r.file))
		m.observe("defines", name, ast.String(r.head.pred))
		m.observe("has a rule for", ast.String(r.file), ast.String(r.head.pred))
		for _, c := range r.conds {
			m.observe("refers to", name, ast.String(c.atom.pred))
		}
		if r.head.key() == "breaks/2" && r.head.args[1].kind == kindString {
			m.observe("lays down", name, ast.String(r.head.args[1].text))
		}
		if r.canonical() != r.text() {
			m.observe("read back differently", name)
		}
		blanks := map[string]bool{}
		for _, a := range r.atoms() {
			for _, v := range a.args {
				if v.kind == kindBlank && !blanks[v.text] {
					blanks[v.text] = true
					m.observe("has the blank", name, ast.String(v.text))
				}
			}
		}
	}
}

func hasBlank(a atom) bool {
	for _, v := range a.args {
		if v.kind == kindBlank {
			return true
		}
	}
	return false
}

func (m *machine) meanings() []*rule {
	var out []*rule
	for _, r := range m.rules {
		if r.fact("means in mangle", 2) && r.head.args[0].kind == kindString && r.head.args[1].kind == kindString {
			out = append(out, r)
		}
	}
	return out
}

func declArgs(arity int) string {
	args := make([]string, arity)
	for i := range args {
		args[i] = "A" + strconv.Itoa(i)
	}
	return strings.Join(args, ", ")
}

func (m *machine) compile() {
	for _, r := range m.meanings() {
		a, err := parseAtom(r.head.args[0].text)
		text := r.head.args[1].text
		if err != nil || strings.HasSuffix(text, ".") || !hasBlank(a) {
			continue
		}
		t := template{args: a.args, text: text}
		for _, v := range a.args {
			if v.kind != kindBlank {
				t.constants++
			}
		}
		m.templates[a.key()] = append(m.templates[a.key()], t)
	}
	for k := range m.templates {
		ts := m.templates[k]
		sort.SliceStable(ts, func(i, j int) bool { return ts[i].constants < ts[j].constants })
	}
	for _, r := range m.meanings() {
		line, want := r.head.args[0].text, r.head.args[1].text
		a, err := parseAtom(line)
		if err != nil {
			m.problem(fmt.Sprintf("%s cannot be read: %v", line, err))
			continue
		}
		got := mangleAtom(a) + "."
		if _, ok := m.templates[a.key()]; ok {
			got, err = m.mangleCondition(condition{atom: a})
			if err != nil {
				m.problem(fmt.Sprintf("%s cannot be said in mangle: %v", line, err))
				continue
			}
		}
		if got != want {
			m.problem(fmt.Sprintf("%s means %s in mangle but engine.go says %s", line, want, got))
		}
	}
	var b strings.Builder
	names := make([]string, 0, len(m.decls))
	for n := range m.decls {
		names = append(names, n)
	}
	sort.Strings(names)
	for _, n := range names {
		fmt.Fprintf(&b, "Decl %s(%s).\n", n, declArgs(m.decls[n]))
	}
	for _, r := range m.rules {
		head := mangleAtom(r.head)
		if len(r.conds) == 0 {
			b.WriteString(head + ".\n")
			continue
		}
		body := make([]string, 0, len(r.conds))
		ok := true
		for _, c := range r.conds {
			s, err := m.mangleCondition(c)
			if err != nil {
				m.problem(fmt.Sprintf("%s cannot be said in mangle: %v", r.name, err))
				ok = false
				break
			}
			body = append(body, s)
		}
		if !ok {
			continue
		}
		r.body = strings.Join(body, ", ")
		b.WriteString(head + " :- " + r.body + ".\n")
	}
	m.program = b.String()
}

func analyze(program string) (info *analysis.ProgramInfo, err error) {
	defer func() {
		if p := recover(); p != nil {
			err = fmt.Errorf("%v", p)
		}
	}()
	unit, err := parse.Unit(strings.NewReader(program))
	if err != nil {
		return nil, err
	}
	return analysis.AnalyzeOneUnit(unit, nil)
}

func evaluate(info *analysis.ProgramInfo, store factstore.FactStore) (err error) {
	defer func() {
		if p := recover(); p != nil {
			err = fmt.Errorf("%v", p)
		}
	}()
	return engine.EvalProgram(info, store)
}

func (m *machine) evaluate() error {
	info, err := analyze(m.program)
	if err != nil {
		return err
	}
	store := factstore.NewIndexedInMemoryStore()
	for _, a := range m.observed {
		store.Add(a)
	}
	for _, a := range m.toolFacts {
		store.Add(a)
	}
	if err := evaluate(info, store); err != nil {
		return err
	}
	m.info = info
	m.store = store
	return nil
}

func (m *machine) facts(phrase string, arity int) [][]ast.Constant {
	var out [][]ast.Constant
	sym := ast.PredicateSym{Symbol: mangleName(phrase), Arity: arity}
	m.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
		out = append(out, constants(a))
		return nil
	})
	return out
}

func (m *machine) pendingCalls() []call {
	var out []call
	for _, row := range m.facts("calls", 3) {
		c := call{command: row[0], tool: textOf(row[1]), input: textOf(row[2])}
		c.key = row[0].String() + "\x00" + row[1].String() + "\x00" + row[2].String()
		if !m.ran[c.key] {
			out = append(out, c)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].key < out[j].key })
	return out
}

func (m *machine) addToolFact(command ast.Constant, field string, v ast.Constant) {
	a := newAtom("returned", command, ast.String(field), v)
	m.toolFacts = append(m.toolFacts, a)
	m.origins[lineOf(a)] = toolsFile
}

func (m *machine) answer() string {
	if len(m.facts("a problem", 1)) > 0 {
		return "broken"
	}
	answers := map[string]bool{}
	for _, row := range m.facts("conforms", 2) {
		if textOf(row[0]) == "the folder" {
			answers[textOf(row[1])] = true
		}
	}
	if len(answers) != 1 {
		return "broken"
	}
	for a := range answers {
		return a
	}
	return "broken"
}

func (m *machine) exitCode(answer string) int {
	for _, row := range m.facts("exits with", 2) {
		if textOf(row[0]) == answer && row[1].Type == ast.NumberType {
			n, _ := row[1].NumberValue()
			return int(n)
		}
	}
	return 2
}

func (m *machine) knowledgeNames() []string {
	var out []string
	for _, row := range m.facts("prints", 2) {
		if textOf(row[0]) == engineFile {
			out = append(out, textOf(row[1]))
		}
	}
	return out
}

func (m *machine) patternKeys(phrase string, knowledge map[string]bool) map[string]bool {
	out := map[string]bool{}
	for _, row := range m.facts(phrase, 2) {
		if !knowledge[textOf(row[0])] {
			continue
		}
		if p, ok := parsePattern(textOf(row[1])); ok {
			out[p.key()] = true
		}
	}
	return out
}

func (m *machine) printed() map[string]bool {
	out := map[string]bool{}
	for _, k := range m.knowledgeNames() {
		out[k] = true
	}
	return out
}

func (m *machine) publishedWhen(answer string) bool {
	knowledge := m.printed()
	for _, row := range m.facts("is published only when", 2) {
		if knowledge[textOf(row[0])] && textOf(row[1]) == answer {
			return true
		}
	}
	return false
}

func (m *machine) derive(all bool) error {
	m.reasonKeys = m.patternKeys("gives reasons for", m.printed())
	var b strings.Builder
	var syms []string
	for sym := range m.info.Decls {
		if nameRe.MatchString(sym.Symbol) && !strings.HasPrefix(sym.Symbol, auxPrefix) {
			syms = append(syms, fmt.Sprintf("Decl %s(%s).\n", sym.Symbol, declArgs(sym.Arity)))
		}
	}
	sort.Strings(syms)
	for _, s := range syms {
		b.WriteString(s)
	}
	type aux struct {
		rule *rule
		vars []string
	}
	var auxes []aux
	for _, r := range m.rules {
		wanted := all || m.reasonKeys[r.head.key()]
		if !wanted {
			continue
		}
		if len(r.conds) == 0 {
			a := newAtom(r.head.pred, constantsOf(r.head.args)...)
			m.derivations = append(m.derivations, derivation{fact: lineOf(a), atom: a, rule: r})
			continue
		}
		if r.body == "" {
			continue
		}
		var vars []string
		seen := map[string]bool{}
		for _, c := range r.conds {
			for _, v := range c.atom.args {
				if v.kind == kindBlank && !seen[varName(v.text)] {
					seen[varName(v.text)] = true
					vars = append(vars, varName(v.text))
				}
			}
		}
		fmt.Fprintf(&b, "%s%d(%s) :- %s.\n", auxPrefix, r.index, strings.Join(vars, ", "), r.body)
		auxes = append(auxes, aux{rule: r, vars: vars})
	}
	if len(auxes) == 0 {
		return nil
	}
	info, err := analyze(b.String())
	if err != nil {
		return err
	}
	if err := evaluate(info, m.store); err != nil {
		return err
	}
	for _, x := range auxes {
		sym := ast.PredicateSym{Symbol: auxPrefix + strconv.Itoa(x.rule.index), Arity: len(x.vars)}
		var found []derivation
		m.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			binding := map[string]value{}
			for i, c := range constants(a) {
				binding[x.vars[i]] = valueOf(c)
			}
			fill := func(at atom) atom {
				out := atom{pred: at.pred, args: make([]value, len(at.args))}
				for i, v := range at.args {
					if v.kind == kindBlank {
						out.args[i] = binding[varName(v.text)]
					} else {
						out.args[i] = v
					}
				}
				return out
			}
			head := fill(x.rule.head)
			d := derivation{atom: newAtom(head.pred, constantsOf(head.args)...), rule: x.rule}
			d.fact = lineOf(d.atom)
			for _, c := range x.rule.conds {
				reason := formatAtom(fill(c.atom))
				if c.negated {
					reason = "not " + reason
				}
				d.reasons = append(d.reasons, reason)
			}
			found = append(found, d)
			return nil
		})
		sort.Slice(found, func(i, j int) bool {
			return strings.Join(found[i].reasons, "\n") < strings.Join(found[j].reasons, "\n")
		})
		m.derivations = append(m.derivations, found...)
	}
	return nil
}

func constantsOf(vs []value) []ast.Constant {
	out := make([]ast.Constant, len(vs))
	for i, v := range vs {
		out[i] = constOf(v)
	}
	return out
}

func (m *machine) giveReasons() {
	for _, d := range m.derivations {
		if !m.reasonKeys[symKey(d.atom.Predicate)] {
			continue
		}
		for _, reason := range d.reasons {
			a := newAtom("holds because", ast.String(d.fact), ast.String(reason))
			m.store.Add(a)
			m.origins[lineOf(a)] = engineFile
		}
	}
}

func (m *machine) allFacts(fn func(ast.Atom)) {
	syms := m.store.ListPredicates()
	sort.Slice(syms, func(i, j int) bool { return symKey(syms[i]) < symKey(syms[j]) })
	for _, sym := range syms {
		if strings.HasPrefix(sym.Symbol, auxPrefix) {
			continue
		}
		m.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			fn(a)
			return nil
		})
	}
}

func (m *machine) print() {
	knowledge := m.printed()
	shown := m.patternKeys("shows", knowledge)
	becauseKey := key("holds because", 2)
	conformsKey := key("conforms", 2)
	reasons := map[string][]string{}
	for _, d := range m.derivations {
		if m.reasonKeys[symKey(d.atom.Predicate)] {
			reasons[d.fact] = append(reasons[d.fact], d.reasons...)
		}
	}
	var plain, reasoned, last []string
	m.allFacts(func(a ast.Atom) {
		k := symKey(a.Predicate)
		switch {
		case k == becauseKey:
			return
		case m.reasonKeys[k]:
			reasoned = append(reasoned, lineOf(a))
		case shown[k] && k == conformsKey:
			last = append(last, lineOf(a))
		case shown[k]:
			plain = append(plain, lineOf(a))
		}
	})
	sort.Strings(plain)
	sort.Strings(reasoned)
	sort.Strings(last)
	written := map[string]bool{}
	var out strings.Builder
	write := func(line string) {
		if !written[line] {
			written[line] = true
			out.WriteString(line + "\n")
		}
	}
	for _, l := range plain {
		write(l)
	}
	for _, l := range reasoned {
		write(l)
		rs := append([]string(nil), reasons[l]...)
		sort.Strings(rs)
		for _, r := range rs {
			write(formatAtom(atom{pred: "holds because", args: []value{str(l), str(r)}}))
		}
	}
	for _, l := range last {
		write(l)
	}
	os.Stdout.WriteString(out.String())
}

func (m *machine) fail() int {
	var out strings.Builder
	for _, p := range m.problems {
		out.WriteString(formatAtom(atom{pred: "a problem", args: []value{str(p)}}) + "\n")
	}
	os.Stdout.WriteString(out.String())
	for _, r := range m.rules {
		if r.fact("exits with", 2) && r.head.args[0].kind == kindString && r.head.args[0].text == "broken" && r.head.args[1].kind == kindNumber {
			return int(r.head.args[1].num)
		}
	}
	for _, f := range m.files {
		for _, r := range f.rules {
			if r.fact("exits with", 2) && r.head.args[0].kind == kindString && r.head.args[0].text == "broken" && r.head.args[1].kind == kindNumber {
				return int(r.head.args[1].num)
			}
		}
	}
	return 2
}

type storeTarget struct {
	name string
	path string
}

func (m *machine) stores() []storeTarget {
	knowledge := m.printed()
	var out []storeTarget
	for _, row := range m.facts("is published to", 2) {
		if !knowledge[textOf(row[0])] {
			continue
		}
		s := textOf(row[1])
		for _, p := range m.facts("is the sqlite file", 2) {
			if textOf(p[0]) != s {
				continue
			}
			path := filepath.Join(m.root, textOf(p[1]))
			if textOf(p[1]) == levelStore {
				path = filepath.Join(m.root, m.level+".db")
			}
			out = append(out, storeTarget{name: s, path: path})
		}
	}
	return out
}

func (m *machine) unpublish() {
	for _, s := range m.stores() {
		os.Remove(s.path)
	}
}

func (m *machine) tableRows(table, answer string) []map[string]any {
	var out []map[string]any
	switch table {
	case "rules":
		for _, r := range m.rules {
			out = append(out, map[string]any{"id": sha16(r.text()), "name": r.name, "file": r.file, "line": r.line, "text": r.text()})
		}
	case "facts":
		seen := map[string]bool{}
		m.allFacts(func(a ast.Atom) {
			line := lineOf(a)
			id := sha16(line)
			if seen[id] {
				return
			}
			seen[id] = true
			origin := m.origins[line]
			if origin == "" {
				origin = derivedOrigin
			}
			out = append(out, map[string]any{"id": id, "text": line, "origin": origin})
		})
	case "derivations", "reasons":
		seen := map[string]bool{}
		for _, d := range m.derivations {
			id := sha16(strings.Join(append([]string{d.fact, d.rule.name}, d.reasons...), "\n"))
			if seen[id] {
				continue
			}
			seen[id] = true
			if table == "derivations" {
				out = append(out, map[string]any{"id": id, "fact_id": sha16(d.fact), "rule": d.rule.name})
				continue
			}
			for i, reason := range d.reasons {
				out = append(out, map[string]any{"derivation_id": id, "position": i + 1, "reason": reason})
			}
		}
	case "certificate":
		out = append(out, map[string]any{"part": partLevel, "subject": "", "value": m.level})
		for _, f := range m.files {
			out = append(out, map[string]any{"part": partHash, "subject": f.name, "value": shaHex(f.data)})
		}
		out = append(out, map[string]any{"part": partAnswer, "subject": "", "value": answer})
	}
	return out
}

func quoteName(s string) string {
	return `"` + strings.ReplaceAll(s, `"`, `""`) + `"`
}

func (m *machine) publish(answer string) error {
	for _, s := range m.stores() {
		if err := m.writeStore(s.path, s.name, answer); err != nil {
			return err
		}
	}
	return nil
}

func (m *machine) writeStore(path, store, answer string) error {
	type column struct {
		position int64
		name     string
	}
	var tables []string
	for _, row := range m.facts("has the table", 2) {
		if textOf(row[0]) == store {
			tables = append(tables, textOf(row[1]))
		}
	}
	sort.Strings(tables)
	columns := map[string][]column{}
	for _, row := range m.facts("has the column", 4) {
		n, _ := row[1].NumberValue()
		columns[textOf(row[0])] = append(columns[textOf(row[0])], column{position: n, name: textOf(row[2])})
	}
	tmp := path + ".new"
	os.Remove(tmp)
	db, err := sql.Open("sqlite", tmp)
	if err != nil {
		return err
	}
	fail := func(err error) error {
		db.Close()
		os.Remove(tmp)
		return err
	}
	tx, err := db.Begin()
	if err != nil {
		return fail(err)
	}
	for _, t := range tables {
		cols := columns[t]
		sort.Slice(cols, func(i, j int) bool { return cols[i].position < cols[j].position })
		if len(cols) == 0 {
			continue
		}
		names := make([]string, len(cols))
		marks := make([]string, len(cols))
		for i, c := range cols {
			names[i] = quoteName(c.name)
			marks[i] = "?"
		}
		if _, err := tx.Exec("CREATE TABLE " + quoteName(t) + " (" + strings.Join(names, ", ") + ")"); err != nil {
			tx.Rollback()
			return fail(err)
		}
		stmt, err := tx.Prepare("INSERT INTO " + quoteName(t) + " VALUES (" + strings.Join(marks, ", ") + ")")
		if err != nil {
			tx.Rollback()
			return fail(err)
		}
		for _, row := range m.tableRows(t, answer) {
			vals := make([]any, len(cols))
			for i, c := range cols {
				vals[i] = row[c.name]
			}
			if _, err := stmt.Exec(vals...); err != nil {
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
	if err := db.Close(); err != nil {
		os.Remove(tmp)
		return err
	}
	return os.Rename(tmp, path)
}
