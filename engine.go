package main

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"unicode"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	changeEnv     = "THIS_RUN_IS_A_CHANGE"
	lawWord       = "breaks"
	brokenAnswer  = "broken"
	plainLanguage = "plain language"
	lostCode      = 2
	factLimit     = 2000000
)

var (
	phraseRe  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z][a-z0-9]*)*$`)
	varRe     = regexp.MustCompile(`^\[[^\[\]]+\]$`)
	numRe     = regexp.MustCompile(`^-?[0-9]+$`)
	patternRe = regexp.MustCompile(`^\[[^\[\]]+\] ([^\[\]]+?)((?: \[[^\[\]]+\])*)$`)
)

var engineDoes = set("loads/2", "means in mangle/2", "uses/3", "exits with/2", "conforms/2", "a problem/1",
	"prints/2", "prints in/2", "prints to/2", "in the knowledge view/1", "shows/2", "gives reasons for/2",
	"creates fact/2")

var engineMakes = set("this run is a change/0", "a problem/1", "misread/1", "has a rule for/2", "defines/2",
	"refers to/2", "lays down/2", "names/2", "holds because/2")

var places = map[string]*os.File{"standard output": os.Stdout, "standard error": os.Stderr}

func set(keys ...string) map[string]bool {
	m := map[string]bool{}
	for _, k := range keys {
		m[k] = true
	}
	return m
}

func engineName() string {
	_, file, _, _ := runtime.Caller(0)
	return filepath.Base(file)
}

type val struct {
	num bool
	n   int64
	s   string
}

func str(s string) val { return val{s: s} }
func num(n int64) val  { return val{num: true, n: n} }
func (v val) field() string {
	if v.num {
		return strconv.FormatInt(v.n, 10)
	}
	return quote(v.s)
}
func (v val) text() string {
	if v.num {
		return strconv.FormatInt(v.n, 10)
	}
	return v.s
}
func (v val) constant() ast.Constant {
	if v.num {
		return ast.Number(v.n)
	}
	return ast.String(v.s)
}

func valOf(b ast.BaseTerm) val {
	if c, ok := b.(ast.Constant); ok {
		switch c.Type {
		case ast.StringType:
			return str(c.Symbol)
		case ast.NumberType:
			return num(c.NumValue)
		}
	}
	return str(b.String())
}

func bare(s string) bool {
	if s == "" || s != strings.TrimSpace(s) || strings.HasPrefix(s, "not ") {
		return false
	}
	if s[0] == '"' || s[0] == '\'' || varRe.MatchString(s) || numRe.MatchString(s) {
		return false
	}
	for _, r := range s {
		if r == ',' || unicode.IsControl(r) {
			return false
		}
	}
	return true
}

func quote(s string) string {
	if bare(s) {
		return s
	}
	return forceQuote(s)
}

func forceQuote(s string) string {
	simple := !strings.ContainsAny(s, "\\\n\t")
	if simple && !strings.Contains(s, `"`) {
		return `"` + s + `"`
	}
	if simple && !strings.Contains(s, `'`) {
		return `'` + s + `'`
	}
	return `"` + strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`, "\t", `\t`).Replace(s) + `"`
}

type term struct {
	isVar bool
	name  string
	v     val
}

func (t term) field() string {
	if t.isVar {
		return "[" + t.name + "]"
	}
	return t.v.field()
}

func termOf(b ast.BaseTerm) term {
	if v, ok := b.(ast.Variable); ok {
		return term{isVar: true, name: plainName(v.Symbol)}
	}
	return term{v: valOf(b)}
}

type atom struct {
	word string
	args []term
	neg  bool
}

func (a atom) key() string { return a.word + "/" + strconv.Itoa(len(a.args)) }

func (a atom) text() string {
	var b strings.Builder
	if a.neg {
		b.WriteString("not ")
	}
	switch len(a.args) {
	case 0:
		b.WriteString(a.word)
	case 1:
		b.WriteString(a.args[0].field() + ", is, " + a.word)
	default:
		b.WriteString(a.args[0].field() + ", " + a.word)
		for _, t := range a.args[1:] {
			f := t.field()
			if a.word == "is" && len(a.args) == 2 && !t.isVar && !t.v.num {
				f = forceQuote(t.v.s)
			}
			b.WriteString(", " + f)
		}
	}
	return b.String()
}

func (a atom) ground() bool {
	for _, t := range a.args {
		if t.isVar {
			return false
		}
	}
	return true
}

func (a atom) bind(m map[string]term) atom {
	out := atom{word: a.word, neg: a.neg}
	for _, t := range a.args {
		if b, ok := m[t.name]; ok && t.isVar {
			t = b
		}
		out.args = append(out.args, t)
	}
	return out
}

func (a atom) atom() ast.Atom {
	args := make([]ast.BaseTerm, len(a.args))
	for i, t := range a.args {
		args[i] = t.v.constant()
	}
	return ast.Atom{Predicate: ast.PredicateSym{Symbol: symOf(a.word), Arity: len(a.args)}, Args: args}
}

type field struct {
	quoted bool
	text   string
}

func splitFields(line string) ([]field, error) {
	var out []field
	i, n := 0, len(line)
	for {
		for i < n && line[i] == ' ' {
			i++
		}
		if i < n && (line[i] == '"' || line[i] == '\'') {
			q := line[i]
			i++
			var b strings.Builder
			closed := false
			for i < n {
				c := line[i]
				if c == '\\' && i+1 < n && strings.IndexByte("\\\"'nt", line[i+1]) >= 0 {
					b.WriteByte(map[byte]byte{'\\': '\\', '"': '"', '\'': '\'', 'n': '\n', 't': '\t'}[line[i+1]])
					i += 2
					continue
				}
				i++
				if c == q {
					closed = true
					break
				}
				b.WriteByte(c)
			}
			if !closed {
				return nil, fmt.Errorf("a quote is never closed")
			}
			for i < n && line[i] == ' ' {
				i++
			}
			out = append(out, field{true, b.String()})
			if i == n {
				return out, nil
			}
			if line[i] != ',' {
				return nil, fmt.Errorf("text follows a closing quote")
			}
			i++
			continue
		}
		j := strings.IndexByte(line[i:], ',')
		t := line[i:]
		if j >= 0 {
			t = line[i : i+j]
		}
		t = strings.TrimRight(t, " ")
		if t == "" {
			return nil, fmt.Errorf("a part is empty")
		}
		out = append(out, field{false, t})
		if j < 0 {
			return out, nil
		}
		i += j + 1
	}
}

func toTerm(f field) (term, error) {
	if f.quoted {
		return term{v: str(f.text)}, nil
	}
	if varRe.MatchString(f.text) {
		return term{isVar: true, name: f.text[1 : len(f.text)-1]}, nil
	}
	if numRe.MatchString(f.text) {
		n, err := strconv.ParseInt(f.text, 10, 64)
		if err != nil {
			return term{}, fmt.Errorf("%s is too big a number", f.text)
		}
		return term{v: num(n)}, nil
	}
	return term{v: str(f.text)}, nil
}

func parseAtom(text string) (atom, error) {
	fs, err := splitFields(text)
	if err != nil {
		return atom{}, err
	}
	if len(fs) == 1 {
		if fs[0].quoted || !phraseRe.MatchString(fs[0].text) {
			return atom{}, fmt.Errorf("one part alone must be lowercase words")
		}
		return atom{word: fs[0].text}, nil
	}
	if len(fs) == 2 {
		return atom{}, fmt.Errorf("it has a subject and a verb but nothing more")
	}
	if fs[1].quoted || !phraseRe.MatchString(fs[1].text) {
		return atom{}, fmt.Errorf("the verb must be lowercase words")
	}
	subject, err := toTerm(fs[0])
	if err != nil {
		return atom{}, err
	}
	if fs[1].text == "is" && len(fs) == 3 && !fs[2].quoted {
		object, err := toTerm(fs[2])
		if err != nil {
			return atom{}, err
		}
		if !object.isVar && !object.v.num {
			if !phraseRe.MatchString(fs[2].text) {
				return atom{}, fmt.Errorf("what something is must be lowercase words")
			}
			return atom{word: fs[2].text, args: []term{subject}}, nil
		}
	}
	a := atom{word: fs[1].text, args: []term{subject}}
	for _, f := range fs[2:] {
		t, err := toTerm(f)
		if err != nil {
			return atom{}, err
		}
		a.args = append(a.args, t)
	}
	return a, nil
}

func parseBody(t string) (atom, error) {
	var rest string
	switch {
	case strings.HasPrefix(t, "if "):
		rest = t[3:]
	case strings.HasPrefix(t, "and "):
		rest = t[4:]
	default:
		return atom{}, fmt.Errorf("an indented line starts with neither if nor and")
	}
	neg := strings.HasPrefix(rest, "not ")
	if neg {
		rest = rest[4:]
	}
	a, err := parseAtom(rest)
	a.neg = neg
	return a, err
}

type clause struct {
	file  string
	id    string
	lines []string
	head  atom
	body  []atom
	bad   bool
	body2 string
	mc    ast.Clause
	back  []string
}

func parseFile(name, text string) ([]*clause, []string) {
	var out []*clause
	var problems []string
	var cur *clause
	for i, raw := range strings.Split(strings.ReplaceAll(text, "\r\n", "\n"), "\n") {
		where := fmt.Sprintf("%s line %d", name, i+1)
		if strings.TrimSpace(raw) == "" {
			cur = nil
			continue
		}
		if raw[0] == ' ' || raw[0] == '\t' {
			if cur == nil {
				problems = append(problems, where+" is indented but follows no rule")
				continue
			}
			cur.lines = append(cur.lines, raw)
			a, err := parseBody(strings.TrimLeft(raw, " \t"))
			if err != nil {
				problems = append(problems, where+" cannot be read: "+err.Error())
				cur.bad = true
				continue
			}
			cur.body = append(cur.body, a)
			continue
		}
		cur = &clause{file: name, id: where, lines: []string{raw}}
		out = append(out, cur)
		a, err := parseAtom(raw)
		if err != nil {
			problems = append(problems, where+" cannot be read: "+err.Error())
			cur.bad = true
			continue
		}
		cur.head = a
	}
	return out, problems
}

func patternOf(s string, zero map[string]bool) (string, int, bool) {
	if !strings.HasPrefix(s, "[") {
		return s, 0, zero[s]
	}
	m := patternRe.FindStringSubmatch(s)
	if m == nil || !phraseRe.MatchString(m[1]) {
		return "", 0, false
	}
	word, arity := m[1], 1+strings.Count(m[2], "[")
	if arity == 1 && strings.HasPrefix(word, "is ") {
		word = word[3:]
	}
	return word, arity, true
}

func symOf(word string) string { return strings.ReplaceAll(word, " ", "_") }

func mangleName(name string) string {
	var b strings.Builder
	for _, w := range strings.Split(name, " ") {
		r := []rune(w)
		if len(r) == 0 {
			b.WriteString("_")
			continue
		}
		b.WriteString(string(unicode.ToUpper(r[0])) + string(r[1:]))
	}
	return b.String()
}

func plainName(v string) string {
	var b strings.Builder
	for i, r := range v {
		if unicode.IsUpper(r) {
			if i > 0 {
				b.WriteByte(' ')
			}
			r = unicode.ToLower(r)
		}
		b.WriteRune(r)
	}
	return b.String()
}

func mangleTerm(t term) string {
	if t.isVar {
		return mangleName(t.name)
	}
	if t.v.num {
		return strconv.FormatInt(t.v.n, 10)
	}
	e, err := ast.Escape(t.v.s, false)
	if err != nil {
		return "<?>"
	}
	return `"` + e + `"`
}

type template struct {
	word string
	text string
	args []string
	pat  ast.Term
	ph   []ast.BaseTerm
}

func tokens(s string) []string {
	var out []string
	for i := 0; i < len(s); {
		j, c := i+1, s[i]
		switch {
		case c == '"' || c == '\'':
			for j < len(s) && s[j] != c {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			j++
		case wordByte(c):
			for j < len(s) && wordByte(s[j]) {
				j++
			}
		}
		if j > len(s) {
			j = len(s)
		}
		out = append(out, s[i:j])
		i = j
	}
	return out
}

func wordByte(c byte) bool {
	return c == '_' || c == ':' || c == '.' || c >= 0x80 ||
		c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

func (tp *template) fill(args []string) string {
	var b strings.Builder
	for _, tk := range tokens(tp.text) {
		for i, a := range tp.args {
			if tk == a {
				tk = args[i]
				break
			}
		}
		b.WriteString(tk)
	}
	return b.String()
}

func (tp *template) match(t ast.Term) (atom, bool) {
	caps := make([]ast.BaseTerm, len(tp.ph))
	if !matchTerm(tp.pat, t, tp.ph, caps) {
		return atom{}, false
	}
	a := atom{word: tp.word}
	for _, c := range caps {
		if c == nil {
			return atom{}, false
		}
		a.args = append(a.args, termOf(c))
	}
	return a, true
}

func matchTerm(p, t ast.Term, ph, caps []ast.BaseTerm) bool {
	switch p := p.(type) {
	case ast.Atom:
		x, ok := t.(ast.Atom)
		return ok && p.Predicate == x.Predicate && matchArgs(p.Args, x.Args, ph, caps)
	case ast.NegAtom:
		x, ok := t.(ast.NegAtom)
		return ok && matchTerm(p.Atom, x.Atom, ph, caps)
	case ast.Eq:
		x, ok := t.(ast.Eq)
		return ok && matchBase(p.Left, x.Left, ph, caps) && matchBase(p.Right, x.Right, ph, caps)
	case ast.Ineq:
		x, ok := t.(ast.Ineq)
		return ok && matchBase(p.Left, x.Left, ph, caps) && matchBase(p.Right, x.Right, ph, caps)
	}
	return false
}

func matchArgs(ps, xs []ast.BaseTerm, ph, caps []ast.BaseTerm) bool {
	if len(ps) != len(xs) {
		return false
	}
	for i := range ps {
		if !matchBase(ps[i], xs[i], ph, caps) {
			return false
		}
	}
	return true
}

func matchBase(p, x ast.BaseTerm, ph, caps []ast.BaseTerm) bool {
	for i, h := range ph {
		if p.Equals(h) {
			if caps[i] == nil {
				caps[i] = x
				return true
			}
			return caps[i].Equals(x)
		}
	}
	if f, ok := p.(ast.ApplyFn); ok {
		g, ok := x.(ast.ApplyFn)
		return ok && f.Function.Symbol == g.Function.Symbol && matchArgs(f.Args, g.Args, ph, caps)
	}
	return p.Equals(x)
}

type job struct {
	command val
	tool    string
	input   val
}

type result struct {
	field string
	value val
}

type state struct {
	self, tools string
	files       []string
	change      string
	instr       map[string]string
	tinstr      map[string]string
	creates     map[string]string
	tcreates    map[string]string
	reasonKeys  map[string]bool
	reasons     map[[2]string]bool
	late        map[string]bool
	results     map[job][]result
}

type auxRule struct {
	c    *clause
	vars []string
}

type world struct {
	st        *state
	all       []*clause
	clauses   []*clause
	problems  []string
	misread   []string
	templates map[string]*template
	tlist     []*template
	zero      map[string]bool
	aux       map[string]auxRule
	store     factstore.SimpleInMemoryStore
	ready     bool
	evalErr   string
}

func (w *world) problem(p string) { w.problems = append(w.problems, p) }

func (w *world) facts(word string, arity int) [][]val {
	if !w.ready {
		return nil
	}
	var out [][]val
	w.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: symOf(word), Arity: arity}), func(a ast.Atom) error {
		row := make([]val, len(a.Args))
		for i, b := range a.Args {
			row[i] = valOf(b)
		}
		out = append(out, row)
		return nil
	})
	sort.Slice(out, func(i, j int) bool { return rowText(out[i]) < rowText(out[j]) })
	return out
}

func naturalLess(a, b string) bool {
	for a != "" && b != "" {
		da, db := digits(a), digits(b)
		if da > 0 && db > 0 {
			x, y := strings.TrimLeft(a[:da], "0"), strings.TrimLeft(b[:db], "0")
			if len(x) != len(y) {
				return len(x) < len(y)
			}
			if x != y {
				return x < y
			}
			a, b = a[da:], b[db:]
			continue
		}
		if a[0] != b[0] {
			return a[0] < b[0]
		}
		a, b = a[1:], b[1:]
	}
	return len(a) < len(b)
}

func digits(s string) int {
	n := 0
	for n < len(s) && s[n] >= '0' && s[n] <= '9' {
		n++
	}
	return n
}

func rowText(row []val) string {
	parts := make([]string, len(row))
	for i, v := range row {
		parts[i] = v.field()
	}
	return strings.Join(parts, ", ")
}

func (w *world) about(word, subject string) []val {
	var out []val
	for _, row := range w.facts(word, 2) {
		if row[0] == str(subject) {
			out = append(out, row[1])
		}
	}
	return out
}

func (w *world) patterns(word, who string) (map[string]string, []string) {
	keys := map[string]string{}
	var bad []string
	for _, v := range w.about(word, who) {
		wd, arity, ok := patternOf(v.text(), w.zero)
		if v.num || !ok {
			bad = append(bad, fmt.Sprintf("%s %s %s, which is not a fact pattern", who, word, v.field()))
			continue
		}
		keys[wd+"/"+strconv.Itoa(arity)] = v.s
	}
	return keys, bad
}

func (w *world) mangleAtom(a atom, templates bool) string {
	args := make([]string, len(a.args))
	for i, t := range a.args {
		args[i] = mangleTerm(t)
	}
	s := symOf(a.word) + "(" + strings.Join(args, ", ") + ")"
	if tp, ok := w.templates[a.key()]; ok && templates {
		s = tp.fill(args)
	}
	if a.neg {
		s = "!" + s
	}
	return s
}

func (w *world) mangleBody(c *clause) string {
	parts := make([]string, len(c.body))
	for i, a := range c.body {
		parts[i] = w.mangleAtom(a, true)
	}
	return strings.Join(parts, ", ")
}

func (w *world) mangleClause(c *clause) string {
	h := w.mangleAtom(c.head, false)
	if len(c.body) == 0 {
		return h + "."
	}
	return h + " :- " + w.mangleBody(c) + "."
}

func (w *world) plainAtom(t ast.Term) (atom, bool) {
	for _, tp := range w.tlist {
		if a, ok := tp.match(t); ok {
			return a, true
		}
	}
	switch x := t.(type) {
	case ast.NegAtom:
		a, ok := w.plainAtom(x.Atom)
		a.neg = true
		return a, ok
	case ast.Atom:
		if strings.HasPrefix(x.Predicate.Symbol, ":") {
			return atom{}, false
		}
		a := atom{word: strings.ReplaceAll(x.Predicate.Symbol, "_", " ")}
		for _, b := range x.Args {
			a.args = append(a.args, termOf(b))
		}
		return a, true
	}
	return atom{}, false
}

func (w *world) plainOf(t ast.Term) string {
	if a, ok := w.plainAtom(t); ok {
		return a.text()
	}
	return t.String()
}

func (w *world) readBack(mc ast.Clause) []string {
	lines := []string{w.plainOf(mc.Head)}
	for i, p := range mc.Premises {
		kw := "    and "
		if i == 0 {
			kw = "    if "
		}
		lines = append(lines, kw+w.plainOf(p))
	}
	return lines
}

func meaning(c *clause) (string, string, bool) {
	if c.bad || len(c.body) > 0 || c.head.key() != "means in mangle/2" {
		return "", "", false
	}
	p, m := c.head.args[0], c.head.args[1]
	if p.isVar || m.isVar || p.v.num || m.v.num {
		return "", "", false
	}
	return p.v.s, m.v.s, true
}

func (w *world) addTemplate(p, m string) error {
	cs, problems := parseFile("", p)
	if len(problems) > 0 || len(cs) != 1 || len(cs[0].body) > 0 {
		return fmt.Errorf("%s is not one fact pattern", quote(p))
	}
	a := cs[0].head
	if _, dup := w.templates[a.key()]; dup {
		return fmt.Errorf("%s already has a meaning in mangle", a.word)
	}
	tp := &template{word: a.word, text: m}
	toks := tokens(m)
	for _, t := range a.args {
		s := mangleTerm(t)
		count := 0
		for _, tk := range toks {
			if tk == s {
				count++
			}
		}
		for _, prev := range tp.args {
			if prev == s {
				count = 0
			}
		}
		if count != 1 {
			return fmt.Errorf("%s must appear once in %s", s, quote(m))
		}
		b, err := parse.BaseTerm(s)
		if err != nil {
			return fmt.Errorf("%s is not mangle", s)
		}
		tp.args = append(tp.args, s)
		tp.ph = append(tp.ph, b)
	}
	pat, err := parse.LiteralOrFormula(m)
	if err != nil {
		return fmt.Errorf("%s is not mangle", quote(m))
	}
	tp.pat = pat
	w.templates[a.key()] = tp
	w.tlist = append(w.tlist, tp)
	return nil
}

func (w *world) translate(c *clause) error {
	if _, ok := w.templates[c.head.key()]; ok {
		return fmt.Errorf("%s has a meaning in mangle and cannot be defined", c.head.word)
	}
	text := w.mangleClause(c)
	mc, err := parse.Clause(text)
	if err != nil {
		return fmt.Errorf("its mangle %s cannot be read", quote(text))
	}
	c.mc, c.body2 = mc, w.mangleBody(c)
	c.back = w.readBack(mc)
	for i, l := range c.lines {
		if i >= len(c.back) || c.back[i] != l {
			w.misread = append(w.misread, l)
		}
	}
	return nil
}

func varsOf(c *clause) []string {
	seen := map[string]bool{}
	var out []string
	for _, a := range append([]atom{c.head}, c.body...) {
		for _, t := range a.args {
			if t.isVar && !seen[t.name] {
				seen[t.name] = true
				out = append(out, t.name)
			}
		}
	}
	return out
}

func analyzeProgram(program []ast.Clause, extra []ast.PredicateSym) (*analysis.ProgramInfo, error) {
	defined := map[ast.PredicateSym]bool{}
	copied := make([]ast.Clause, len(program))
	for i, c := range program {
		defined[c.Head.Predicate] = true
		c.Premises = append([]ast.Term(nil), c.Premises...)
		copied[i] = c
	}
	decls := map[ast.PredicateSym]ast.Decl{}
	need := func(p ast.PredicateSym) {
		if !defined[p] && !strings.HasPrefix(p.Symbol, ":") {
			decls[p] = ast.NewSyntheticDeclFromSym(p)
		}
	}
	for _, c := range copied {
		for _, t := range c.Premises {
			switch x := t.(type) {
			case ast.Atom:
				need(x.Predicate)
			case ast.NegAtom:
				need(x.Atom.Predicate)
			}
		}
	}
	for _, p := range extra {
		need(p)
	}
	return analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: copied}, decls)
}

func (s *state) build() *world {
	w := &world{st: s, templates: map[string]*template{}, zero: map[string]bool{}, aux: map[string]auxRule{}}
	if len(s.files) == 0 {
		w.problem(s.self + " is told no file to load")
	}
	for _, f := range s.files {
		data, err := os.ReadFile(f)
		if err != nil {
			w.problem(f + " cannot be read")
			continue
		}
		cs, problems := parseFile(f, string(data))
		w.all = append(w.all, cs...)
		w.problems = append(w.problems, problems...)
	}
	means := s.instr["means in mangle/2"] != ""
	if means {
		for _, c := range w.all {
			if p, m, ok := meaning(c); ok && !strings.HasSuffix(m, ".") {
				if err := w.addTemplate(p, m); err != nil {
					w.problem(c.id + " gives no meaning: " + err.Error())
				}
			}
		}
	}
	var good []*clause
	for _, c := range w.all {
		if c.bad {
			continue
		}
		if err := w.translate(c); err != nil {
			w.problem(c.id + " cannot be used: " + err.Error())
			continue
		}
		good = append(good, c)
	}
	if means {
		for _, c := range w.all {
			p, m, ok := meaning(c)
			if !ok || !strings.HasSuffix(m, ".") {
				continue
			}
			cs, problems := parseFile("", p)
			if len(problems) > 0 || len(cs) != 1 {
				w.problem(c.id + " gives a meaning to something that cannot be read")
				continue
			}
			if got := w.mangleClause(cs[0]); got != m {
				w.problem(fmt.Sprintf("%s says %s means %s in mangle, but it means %s", c.id, quote(p), quote(m), quote(got)))
			}
		}
	}
	for k := range engineMakes {
		if strings.HasSuffix(k, "/0") {
			w.zero[strings.TrimSuffix(k, "/0")] = true
		}
	}
	for _, c := range good {
		for _, a := range append([]atom{c.head}, c.body...) {
			if len(a.args) == 0 {
				w.zero[a.word] = true
			}
		}
	}
	var program []ast.Clause
	var owners []*clause
	for _, c := range good {
		program = append(program, c.mc)
		owners = append(owners, c)
	}
	for i, c := range good {
		if len(c.body) == 0 || !s.reasonKeys[c.head.key()] {
			continue
		}
		vars := varsOf(c)
		names := make([]string, len(vars))
		for j, v := range vars {
			names[j] = mangleName(v)
		}
		sym := fmt.Sprintf("reason__%d", i)
		mc, err := parse.Clause(sym + "(" + strings.Join(names, ", ") + ") :- " + c.body2 + ".")
		if err != nil {
			continue
		}
		program = append(program, mc)
		owners = append(owners, c)
		w.aux[sym] = auxRule{c, vars}
	}
	var extra []ast.PredicateSym
	for k := range engineMakes {
		extra = append(extra, keySym(k))
	}
	for k := range toolsMake {
		extra = append(extra, keySym(k))
	}
	info, err := analyzeProgram(program, extra)
	if err != nil {
		var keep []ast.Clause
		dropped := map[*clause]bool{}
		for i, c := range program {
			if _, e := analyzeProgram([]ast.Clause{c}, nil); e != nil {
				if !dropped[owners[i]] {
					w.problem(owners[i].id + " cannot be used: " + e.Error())
				}
				dropped[owners[i]] = true
			}
		}
		for i, c := range program {
			if !dropped[owners[i]] {
				keep = append(keep, c)
			}
		}
		for sym, a := range w.aux {
			if dropped[a.c] {
				delete(w.aux, sym)
			}
		}
		var kept []*clause
		for _, c := range good {
			if !dropped[c] {
				kept = append(kept, c)
			}
		}
		good = kept
		info, err = analyzeProgram(keep, extra)
		if err != nil {
			w.problem("the knowledge cannot be used: " + err.Error())
		}
	}
	w.clauses = good
	w.store = factstore.NewSimpleInMemoryStore()
	for _, a := range w.made() {
		w.store.Add(a)
	}
	if info != nil {
		if err := engine.EvalProgram(info, w.store, engine.WithCreatedFactLimit(factLimit)); err != nil {
			w.evalErr = "the knowledge cannot be evaluated: " + err.Error()
		}
	}
	w.ready = true
	return w
}

func keySym(k string) ast.PredicateSym {
	i := strings.LastIndexByte(k, '/')
	n, _ := strconv.Atoi(k[i+1:])
	return ast.PredicateSym{Symbol: symOf(k[:i]), Arity: n}
}

func (w *world) made() []ast.Atom {
	s := w.st
	var out []ast.Atom
	add := func(creates map[string]string, word string, args ...val) {
		a := atom{word: word}
		for _, v := range args {
			a.args = append(a.args, term{v: v})
		}
		if creates[a.key()] != "" {
			out = append(out, a.atom())
		}
	}
	if s.change != "" {
		add(s.creates, "this run is a change")
	}
	for _, p := range w.problems {
		add(s.creates, "a problem", str(p))
	}
	for p := range s.late {
		add(s.creates, "a problem", str(p))
	}
	for _, l := range w.misread {
		add(s.creates, "misread", str(l))
	}
	for _, c := range w.clauses {
		add(s.creates, "has a rule for", str(c.file), str(c.head.word))
		add(s.creates, "defines", str(c.id), str(c.head.word))
		for _, a := range c.body {
			add(s.creates, "refers to", str(c.id), str(a.word))
		}
		if c.head.key() == lawWord+"/2" && !c.head.args[1].isVar {
			add(s.creates, "lays down", str(c.id), c.head.args[1].v)
		}
		for _, a := range append([]atom{c.head}, c.body...) {
			for _, t := range a.args {
				if t.isVar || t.v.num {
					continue
				}
				if word, _, ok := patternOf(t.v.s, w.zero); ok {
					add(s.creates, "names", t.v, str(word))
				}
			}
		}
	}
	for r := range s.reasons {
		add(s.creates, "holds because", str(r[0]), str(r[1]))
	}
	for j, rs := range s.results {
		for _, r := range rs {
			add(s.tcreates, "returned", j.command, str(r.field), r.value)
		}
	}
	return out
}

func (w *world) reasons() map[[2]string]bool {
	out := map[[2]string]bool{}
	for sym, a := range w.aux {
		w.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: sym, Arity: len(a.vars)}), func(f ast.Atom) error {
			m := map[string]term{}
			for i, v := range a.vars {
				m[v] = termOf(f.Args[i])
			}
			head := a.c.head.bind(m).text()
			out[[2]string{head, a.c.id}] = true
			for _, b := range a.c.body {
				out[[2]string{head, b.bind(m).text()}] = true
			}
			return nil
		})
	}
	for _, c := range w.clauses {
		if len(c.body) == 0 && w.st.reasonKeys[c.head.key()] && c.head.ground() {
			out[[2]string{c.head.text(), c.id}] = true
		}
	}
	return out
}

type plan struct {
	view val
	out  *os.File
}

func (s *state) plans(w *world) ([]plan, []string) {
	if s.instr["prints/2"] == "" {
		return nil, nil
	}
	views := w.about("prints", s.self)
	if len(views) == 0 {
		return nil, nil
	}
	var problems []string
	var langs, where []val
	if s.instr["prints in/2"] != "" {
		langs = w.about("prints in", s.self)
	}
	if s.instr["prints to/2"] != "" {
		where = w.about("prints to", s.self)
	}
	if len(langs) != 1 || langs[0] != str(plainLanguage) {
		problems = append(problems, s.self+" prints only in "+plainLanguage)
	}
	if len(where) != 1 || places[where[0].text()] == nil {
		problems = append(problems, s.self+" prints to one place, standard output or standard error")
		return nil, problems
	}
	var out []plan
	for _, v := range views {
		out = append(out, plan{v, places[where[0].text()]})
	}
	return out, problems
}

func (s *state) answer(w *world, extra []string) (int, []string) {
	problems := append([]string{}, extra...)
	broken := len(w.problems) > 0 || len(s.late) > 0 || len(extra) > 0
	if s.instr["a problem/1"] != "" && len(w.facts("a problem", 1)) > 0 {
		broken = true
	}
	answer := str(brokenAnswer)
	if !broken {
		answers := map[val]bool{}
		if s.instr["conforms/2"] != "" {
			for _, row := range w.facts("conforms", 2) {
				answers[row[1]] = true
			}
		}
		if len(answers) == 1 {
			for a := range answers {
				answer = a
			}
		} else {
			problems = append(problems, fmt.Sprintf("the folder conforms with %d answers", len(answers)))
		}
	}
	codes := map[int64]bool{}
	if s.instr["exits with/2"] != "" {
		for _, row := range w.facts("exits with", 2) {
			if row[0] == answer && row[1].num {
				codes[row[1].n] = true
			}
		}
	}
	if len(codes) != 1 {
		return lostCode, append(problems, answer.field()+" exits with no single code")
	}
	for c := range codes {
		return int(c), problems
	}
	return lostCode, problems
}

func sameKeys(a, b map[string]string) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		if b[k] != v {
			return false
		}
	}
	return true
}

func (s *state) absorb(w *world) bool {
	instr, bad := w.patterns("executes instruction", s.self)
	tinstr, bad2 := w.patterns("executes instruction", s.tools)
	bad = append(bad, bad2...)
	creates, tcreates := map[string]string{}, map[string]string{}
	if instr["creates fact/2"] != "" {
		var b1, b2 []string
		creates, b1 = w.patterns("creates fact", s.self)
		tcreates, b2 = w.patterns("creates fact", s.tools)
		bad = append(append(bad, b1...), b2...)
	}
	reasonKeys := map[string]bool{}
	if instr["gives reasons for/2"] != "" {
		for _, row := range w.facts("gives reasons for", 2) {
			if word, arity, ok := patternOf(row[1].text(), w.zero); ok && !row[1].num {
				reasonKeys[word+"/"+strconv.Itoa(arity)] = true
			}
		}
	}
	reasons := w.reasons()
	late := append([]string{}, bad...)
	if w.evalErr != "" {
		late = append(late, w.evalErr)
	}
	for k, p := range instr {
		if !engineDoes[k] {
			late = append(late, s.self+" cannot execute "+p)
		}
	}
	for k, p := range tinstr {
		if !toolsDo[k] {
			late = append(late, s.tools+" cannot execute "+p)
		}
	}
	for k, p := range creates {
		if !engineMakes[k] {
			late = append(late, s.self+" cannot create "+p)
		}
	}
	for k, p := range tcreates {
		if !toolsMake[k] {
			late = append(late, s.tools+" cannot create "+p)
		}
	}
	if instr["loads/2"] != "" {
		for _, f := range w.about("loads", s.self) {
			if f.num || filepath.Base(f.s) != f.s || f.s == ".." {
				late = append(late, s.self+" loads only files in the folder, not "+f.field())
			}
		}
	}
	changed := !sameKeys(instr, s.instr) || !sameKeys(tinstr, s.tinstr) || !sameKeys(creates, s.creates) ||
		!sameKeys(tcreates, s.tcreates) || len(reasonKeys) != len(s.reasonKeys) || len(reasons) != len(s.reasons)
	for k := range reasonKeys {
		changed = changed || !s.reasonKeys[k]
	}
	for r := range reasons {
		changed = changed || !s.reasons[r]
	}
	fresh := set(late...)
	changed = changed || len(fresh) != len(s.late)
	for p := range fresh {
		changed = changed || !s.late[p]
	}
	s.late = fresh
	s.instr, s.tinstr, s.creates, s.tcreates, s.reasonKeys, s.reasons = instr, tinstr, creates, tcreates, reasonKeys, reasons
	return changed
}

func (s *state) loadMore(w *world) bool {
	if s.instr["loads/2"] == "" {
		return false
	}
	added := false
	for _, f := range w.about("loads", s.self) {
		if f.num || filepath.Base(f.s) != f.s || f.s == ".." {
			continue
		}
		known := false
		for _, g := range s.files {
			known = known || g == f.s
		}
		if info, err := os.Stat(f.s); known || err != nil || !info.Mode().IsRegular() {
			continue
		}
		s.files = append(s.files, f.s)
		added = true
	}
	return added
}

func (s *state) settle() *world {
	for round := 0; round < 100; round++ {
		w := s.build()
		if s.absorb(w) || s.loadMore(w) || s.runJobs(w) {
			continue
		}
		return w
	}
	w := s.build()
	w.problem("the knowledge never settles")
	return w
}

func (s *state) writeView(out *bufio.Writer, w *world, view val) {
	first := true
	if s.instr["in the knowledge view/1"] != "" {
		in := map[val]bool{}
		for _, row := range w.facts("in the knowledge view", 1) {
			in[row[0]] = true
		}
		multi := false
		for _, c := range w.clauses {
			if !in[str(c.id)] {
				continue
			}
			if !first && (multi || len(c.back) > 1) {
				out.WriteString("\n")
			}
			for _, l := range c.back {
				out.WriteString(l + "\n")
			}
			first, multi = false, len(c.back) > 1
		}
	}
	if s.instr["shows/2"] == "" {
		return
	}
	shown := map[string]bool{}
	var keys []string
	for _, row := range w.facts("shows", 2) {
		if row[0] != view || row[1].num {
			continue
		}
		if word, arity, ok := patternOf(row[1].s, w.zero); ok && !shown[word+"/"+strconv.Itoa(arity)] {
			shown[word+"/"+strconv.Itoa(arity)] = true
			keys = append(keys, word+"/"+strconv.Itoa(arity))
		}
	}
	sort.Strings(keys)
	for _, k := range keys {
		sym := keySym(k)
		var lines []string
		for _, row := range w.facts(strings.ReplaceAll(sym.Symbol, "_", " "), sym.Arity) {
			a := atom{word: k[:strings.LastIndexByte(k, '/')]}
			for _, v := range row {
				a.args = append(a.args, term{v: v})
			}
			lines = append(lines, a.text())
		}
		sort.Slice(lines, func(i, j int) bool { return naturalLess(lines[i], lines[j]) })
		if len(lines) > 0 && !first {
			out.WriteString("\n")
		}
		for _, l := range lines {
			out.WriteString(l + "\n")
			first = false
		}
	}
}

func main() {
	s := &state{
		self:       engineName(),
		tools:      toolsName(),
		change:     os.Getenv(changeEnv),
		instr:      map[string]string{},
		tinstr:     map[string]string{},
		creates:    map[string]string{},
		tcreates:   map[string]string{},
		reasonKeys: map[string]bool{},
		reasons:    map[[2]string]bool{},
		late:       map[string]bool{},
		results:    map[job][]result{},
	}
	if len(os.Args) > 1 {
		s.files = []string{os.Args[1]}
	}
	w := s.settle()
	plans, planProblems := s.plans(w)
	for _, p := range plans {
		out := bufio.NewWriter(p.out)
		s.writeView(out, w, p.view)
		out.Flush()
	}
	code, finalProblems := s.answer(w, planProblems)
	var problems []string
	problems = append(append(problems, w.problems...), finalProblems...)
	for p := range s.late {
		problems = append(problems, p)
	}
	sort.Strings(problems)
	for _, p := range problems {
		fmt.Fprintln(os.Stderr, p)
	}
	os.Exit(code)
}
