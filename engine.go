package main

import (
	"bufio"
	"fmt"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

const (
	self         = "engine.go"
	changeSignal = "THIS_RUN_IS_A_CHANGE"
	brokenCode   = 2
	madeOrder    = 1 << 40
	derivedOrder = 1 << 50
)

var (
	wordsShape  = regexp.MustCompile(`^[a-z][a-z0-9]*( [a-z0-9]+)*$`)
	blankShape  = regexp.MustCompile(`^\[([^\[\]]*)\]$`)
	numberShape = regexp.MustCompile(`^-?[0-9]+$`)
	blankInText = regexp.MustCompile(`\[[^\[\]]*\]`)
)

type value struct {
	number bool
	n      int64
	s      string
}

func text(s string) value { return value{s: s} }

func count(n int64) value { return value{number: true, n: n} }

func (v value) String() string {
	if v.number {
		return strconv.FormatInt(v.n, 10)
	}
	return v.s
}

func (v value) key() string {
	if v.number {
		return "n" + v.String()
	}
	return "s" + v.s
}

type term struct {
	blank string
	val   value
}

type atom struct {
	pred string
	args []term
}

type condition struct {
	negated bool
	atom    atom
}

type rule struct {
	file    string
	line    int
	id      string
	head    atom
	conds   []condition
	misread bool
	gap     bool
}

func (r *rule) where() string { return r.id }

func (r *rule) blanks() []string {
	var names []string
	seen := map[string]bool{}
	visit := func(a atom) {
		for _, t := range a.args {
			if t.blank != "" && !seen[t.blank] {
				seen[t.blank] = true
				names = append(names, t.blank)
			}
		}
	}
	visit(r.head)
	for _, c := range r.conds {
		visit(c.atom)
	}
	return names
}

func (r *rule) atoms() []atom {
	all := []atom{r.head}
	for _, c := range r.conds {
		all = append(all, c.atom)
	}
	return all
}

type fact struct {
	pred string
	args []value
}

func (f fact) key() string {
	parts := []string{f.pred}
	for _, v := range f.args {
		parts = append(parts, v.key())
	}
	return strings.Join(parts, "\x00")
}

func (f fact) atom() atom {
	a := atom{pred: f.pred}
	for _, v := range f.args {
		a.args = append(a.args, term{val: v})
	}
	return a
}

type pattern struct {
	text  string
	pred  string
	slots []string
}

type template struct {
	arity  int
	tokens []string
	slots  []int
}

type reasonRule struct {
	rule *rule
	name string
	vars []string
}

type knowledge struct {
	change    bool
	files     []string
	loaded    map[string]bool
	rules     []*rule
	problems  []string
	seen      map[string]bool
	order     map[string]int
	returned  []fact
	ran       map[string]bool
	templates map[string]template
	known     map[string][]fact
	extra     map[string][]fact
	aux       map[*rule]reasonRule
	auxFacts  map[string][]fact
	plain     map[string]string
	evaluated bool
}

func oneLine(s string) string {
	return strings.ReplaceAll(strings.ReplaceAll(s, "\r", ""), "\n", " ")
}

func readPart(s string) (term, error) {
	if s == "" {
		return term{}, fmt.Errorf("a part is empty")
	}
	if m := blankShape.FindStringSubmatch(s); m != nil {
		if !wordsShape.MatchString(m[1]) {
			return term{}, fmt.Errorf("the blank %s is not lowercase words", s)
		}
		return term{blank: m[1]}, nil
	}
	if numberShape.MatchString(s) {
		n, err := strconv.ParseInt(s, 10, 64)
		if err != nil {
			return term{}, fmt.Errorf("the number %s is too big", s)
		}
		return term{val: count(n)}, nil
	}
	return term{val: text(s)}, nil
}

func readParts(s string) ([]term, error) {
	var parts []term
	rest := s
	for {
		lead := strings.TrimLeft(rest, " \t")
		if lead != "" && (lead[0] == '"' || lead[0] == '\'') {
			end := strings.IndexByte(lead[1:], lead[0])
			if end < 0 {
				return nil, fmt.Errorf("a quote is never closed")
			}
			parts = append(parts, term{val: text(lead[1 : 1+end])})
			after := strings.TrimLeft(lead[2+end:], " \t")
			if after == "" {
				return parts, nil
			}
			if after[0] != ',' {
				return nil, fmt.Errorf("text follows a closing quote")
			}
			rest = after[1:]
			continue
		}
		comma := strings.IndexByte(rest, ',')
		piece := rest
		if comma >= 0 {
			piece = rest[:comma]
		}
		t, err := readPart(strings.TrimSpace(piece))
		if err != nil {
			return nil, err
		}
		parts = append(parts, t)
		if comma < 0 {
			return parts, nil
		}
		rest = rest[comma+1:]
	}
}

func predicateWords(t term) (string, bool) {
	if t.blank != "" || t.val.number || !wordsShape.MatchString(t.val.s) {
		return "", false
	}
	return t.val.s, true
}

func readAtom(s string) (atom, error) {
	parts, err := readParts(s)
	if err != nil {
		return atom{}, fmt.Errorf("%q cannot be read: %v", s, err)
	}
	switch len(parts) {
	case 1:
		pred, ok := predicateWords(parts[0])
		if !ok {
			return atom{}, fmt.Errorf("%q has one part, so it must be a predicate of lowercase words", s)
		}
		return atom{pred: pred}, nil
	case 2:
		return atom{}, fmt.Errorf("%q has two parts, but a line has one part or at least three", s)
	}
	verb, ok := predicateWords(parts[1])
	if !ok {
		return atom{}, fmt.Errorf("%q has no predicate of lowercase words in its second part", s)
	}
	if verb != "is" {
		return atom{pred: verb, args: append([]term{parts[0]}, parts[2:]...)}, nil
	}
	if len(parts) != 3 {
		return atom{}, fmt.Errorf("%q uses is, so it must have three parts", s)
	}
	pred, ok := predicateWords(parts[2])
	if !ok {
		return atom{}, fmt.Errorf("%q uses is, so its third part must be a predicate of lowercase words", s)
	}
	return atom{pred: pred, args: parts[:1]}, nil
}

func readCondition(s string) (condition, error) {
	var rest string
	switch {
	case strings.HasPrefix(s, "if "):
		rest = s[3:]
	case strings.HasPrefix(s, "and "):
		rest = s[4:]
	default:
		return condition{}, fmt.Errorf("%q is indented, so it must start with if or and", s)
	}
	c := condition{}
	if strings.HasPrefix(rest, "not ") {
		c.negated = true
		rest = rest[4:]
	}
	a, err := readAtom(rest)
	c.atom = a
	return c, err
}

func readText(file, content string) ([]*rule, []string) {
	var rules []*rule
	var problems []string
	var current *rule
	skipping, gap := false, false
	lines := strings.Split(content, "\n")
	if n := len(lines); n > 0 && lines[n-1] == "" {
		lines = lines[:n-1]
	}
	for i, line := range lines {
		where := fmt.Sprintf("%s line %d: ", file, i+1)
		if strings.TrimSpace(line) == "" {
			current, skipping, gap = nil, false, true
			continue
		}
		if line[0] == ' ' || line[0] == '\t' {
			if skipping {
				continue
			}
			if current == nil {
				problems = append(problems, where+"this condition follows no rule")
				continue
			}
			c, err := readCondition(strings.TrimLeft(line, " \t"))
			if err != nil {
				problems = append(problems, where+err.Error())
				continue
			}
			if showCondition(len(current.conds), c) != line {
				current.misread = true
			}
			current.conds = append(current.conds, c)
			continue
		}
		head, err := readAtom(line)
		if err != nil {
			problems = append(problems, where+err.Error())
			current, skipping = nil, true
			continue
		}
		current = &rule{file: file, line: i + 1, id: fmt.Sprintf("%s line %d", file, i+1), head: head, misread: showAtom(head) != line, gap: gap}
		skipping, gap = false, false
		rules = append(rules, current)
	}
	return rules, problems
}

func needsQuotes(s string) bool {
	return s == "" || strings.Contains(s, ",") || s != strings.TrimSpace(s) ||
		s[0] == '"' || s[0] == '\'' || strings.HasPrefix(s, "not ") ||
		numberShape.MatchString(s) || blankShape.MatchString(s)
}

func showValue(v value) string {
	if v.number || !needsQuotes(v.s) {
		return v.String()
	}
	if !strings.Contains(v.s, `"`) {
		return `"` + v.s + `"`
	}
	if !strings.Contains(v.s, "'") {
		return "'" + v.s + "'"
	}
	return `"` + strings.ReplaceAll(v.s, `"`, "'") + `"`
}

func showTerm(t term) string {
	if t.blank != "" {
		return "[" + t.blank + "]"
	}
	return showValue(t.val)
}

func showAtom(a atom) string {
	switch len(a.args) {
	case 0:
		return a.pred
	case 1:
		return showTerm(a.args[0]) + ", is, " + a.pred
	}
	parts := []string{showTerm(a.args[0]), a.pred}
	for _, t := range a.args[1:] {
		parts = append(parts, showTerm(t))
	}
	return strings.Join(parts, ", ")
}

func showCondition(i int, c condition) string {
	lead := "    if "
	if i > 0 {
		lead = "    and "
	}
	if c.negated {
		lead += "not "
	}
	return lead + showAtom(c.atom)
}

func showFact(f fact) string { return showAtom(f.atom()) }

func readPattern(s string) (pattern, error) {
	p := pattern{text: s}
	spots := blankInText.FindAllStringIndex(s, -1)
	if len(spots) == 0 {
		if !wordsShape.MatchString(s) {
			return p, fmt.Errorf("the fact pattern %q names no predicate", s)
		}
		p.pred = s
		return p, nil
	}
	if strings.TrimSpace(s[:spots[0][0]]) != "" {
		return p, fmt.Errorf("the fact pattern %q must start with a blank", s)
	}
	var between []string
	for i, spot := range spots {
		name := s[spot[0]+1 : spot[1]-1]
		if !wordsShape.MatchString(name) {
			return p, fmt.Errorf("the fact pattern %q has a blank that is not lowercase words", s)
		}
		p.slots = append(p.slots, name)
		end := len(s)
		if i+1 < len(spots) {
			end = spots[i+1][0]
		}
		between = append(between, strings.TrimSpace(s[spot[1]:end]))
	}
	words := between[0]
	for _, rest := range between[1:] {
		if rest != "" {
			return p, fmt.Errorf("the fact pattern %q has words after its second blank", s)
		}
	}
	if len(spots) == 1 {
		if !strings.HasPrefix(words, "is ") {
			return p, fmt.Errorf("the fact pattern %q has one blank, so it must say is", s)
		}
		words = words[3:]
	}
	if !wordsShape.MatchString(words) || (len(spots) > 1 && words == "is") {
		return p, fmt.Errorf("the fact pattern %q names no predicate", s)
	}
	p.pred = words
	return p, nil
}

func baseName(blank string) string {
	for _, lead := range []string{"any ", "other "} {
		if strings.HasPrefix(blank, lead) {
			return blank[len(lead):]
		}
	}
	return blank
}

func mangleName(pred string) string { return strings.ReplaceAll(pred, " ", "_") }

func mangleVar(blank string) string {
	var b strings.Builder
	for _, word := range strings.Fields(blank) {
		b.WriteString(strings.ToUpper(word[:1]) + word[1:])
	}
	return b.String()
}

func mangleString(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch {
		case r == '\\':
			b.WriteString(`\\`)
		case r == '"':
			b.WriteString(`\"`)
		case r == '\n':
			b.WriteString(`\n`)
		case r == '\t':
			b.WriteString(`\t`)
		case r < 0x20 || r == 0x7f:
			fmt.Fprintf(&b, `\x%02x`, r)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func mangleValue(v value) string {
	if v.number {
		return v.String()
	}
	return mangleString(v.s)
}

func mangleTerm(t term) string {
	if t.blank != "" {
		return mangleVar(t.blank)
	}
	return mangleValue(t.val)
}

func mangleAtom(a atom) string {
	args := make([]string, len(a.args))
	for i, t := range a.args {
		args[i] = mangleTerm(t)
	}
	return mangleName(a.pred) + "(" + strings.Join(args, ", ") + ")"
}

func mangleTokens(s string) []string {
	var tokens []string
	word := func(c byte) bool {
		return c == '_' || c == ':' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
	}
	for i := 0; i < len(s); {
		j := i + 1
		switch {
		case s[i] == '"':
			for j < len(s) && s[j] != '"' {
				if s[j] == '\\' {
					j++
				}
				j++
			}
			j = min(j+1, len(s))
		case word(s[i]):
			for j < len(s) && word(s[j]) {
				j++
			}
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens
}

func makeTemplate(a atom, mangle string) template {
	t := template{arity: len(a.args), tokens: mangleTokens(mangle)}
	for _, token := range t.tokens {
		slot := -1
		for i, arg := range a.args {
			if mangleTerm(arg) == token {
				slot = i
				break
			}
		}
		t.slots = append(t.slots, slot)
	}
	return t
}

func (t template) fill(a atom) string {
	var b strings.Builder
	for i, token := range t.tokens {
		if t.slots[i] >= 0 {
			token = mangleTerm(a.args[t.slots[i]])
		}
		b.WriteString(token)
	}
	return b.String()
}

func newKnowledge() *knowledge {
	return &knowledge{
		loaded:   map[string]bool{},
		seen:     map[string]bool{},
		order:    map[string]int{},
		ran:      map[string]bool{},
		known:    map[string][]fact{},
		extra:    map[string][]fact{},
		aux:      map[*rule]reasonRule{},
		auxFacts: map[string][]fact{},
		change:   os.Getenv(changeSignal) != "",
	}
}

func (k *knowledge) problem(s string) {
	s = oneLine(s)
	if !k.seen[s] {
		k.seen[s] = true
		k.problems = append(k.problems, s)
	}
}

func (k *knowledge) facts(pred string) []fact { return k.known[pred] }

func (k *knowledge) all(pred string) []fact {
	return append(append([]fact{}, k.known[pred]...), k.extra[pred]...)
}

func (k *knowledge) only(pred, subject string) (string, error) {
	var found []string
	for _, f := range k.facts(pred) {
		if len(f.args) == 2 && f.args[0] == text(subject) {
			found = append(found, f.args[1].String())
		}
	}
	if len(found) != 1 {
		return "", fmt.Errorf("%s needs one fact saying what it %s, not %d", subject, pred, len(found))
	}
	return found[0], nil
}

func (k *knowledge) load(file string) {
	k.loaded[file] = true
	index := len(k.files)
	k.files = append(k.files, file)
	content, err := os.ReadFile(file)
	if os.IsNotExist(err) {
		return
	}
	if err != nil {
		k.problem(fmt.Sprintf("%s cannot be read: %v", file, err))
		return
	}
	rules, problems := readText(file, string(content))
	for _, p := range problems {
		k.problem(p)
	}
	for _, r := range rules {
		if len(r.conds) > 0 || len(r.blanks()) > 0 {
			continue
		}
		f := fact{pred: r.head.pred}
		for _, t := range r.head.args {
			f.args = append(f.args, t.val)
		}
		if _, ok := k.order[f.key()]; !ok {
			k.order[f.key()] = index<<24 + r.line
		}
	}
	k.rules = append(k.rules, rules...)
}

func (k *knowledge) readTemplates() {
	k.templates = map[string]template{}
	type check struct {
		r     *rule
		plain atom
		said  string
	}
	var checks []check
	for _, r := range k.rules {
		if r.head.pred != "means in mangle" || len(r.conds) > 0 || len(r.head.args) != 2 {
			continue
		}
		plain, said := r.head.args[0], r.head.args[1]
		if plain.blank != "" || said.blank != "" || plain.val.number || said.val.number {
			continue
		}
		a, err := readAtom(plain.val.s)
		if err != nil {
			k.problem(r.where() + ": " + err.Error())
			continue
		}
		if strings.HasSuffix(said.val.s, ".") {
			checks = append(checks, check{r, a, said.val.s})
			continue
		}
		k.templates[a.pred] = makeTemplate(a, said.val.s)
	}
	for _, c := range checks {
		got, err := k.mangleRule(&rule{head: c.plain})
		if err == nil && got != c.said {
			err = fmt.Errorf("engine.go reads %s as %s", c.plain.pred, got)
		}
		if err != nil {
			k.problem(fmt.Sprintf("%s: %s should mean %s in mangle, but %v", c.r.where(), showAtom(c.plain), c.said, err))
		}
	}
}

func (k *knowledge) mangleCondition(c condition) (string, error) {
	s := mangleAtom(c.atom)
	if t, ok := k.templates[c.atom.pred]; ok {
		if len(c.atom.args) != t.arity {
			return "", fmt.Errorf("%s takes %d parts after its subject", c.atom.pred, t.arity-1)
		}
		s = t.fill(c.atom)
	}
	if c.negated {
		s = "!" + s
	}
	return s, nil
}

func (k *knowledge) mangleBody(r *rule) (string, error) {
	var body []string
	for _, c := range r.conds {
		s, err := k.mangleCondition(c)
		if err != nil {
			return "", err
		}
		body = append(body, s)
	}
	return strings.Join(body, ", "), nil
}

func (k *knowledge) mangleRule(r *rule) (string, error) {
	if _, ok := k.templates[r.head.pred]; ok {
		return "", fmt.Errorf("%s is built into mangle, so no rule can define it", r.head.pred)
	}
	head := mangleAtom(r.head)
	if len(r.conds) == 0 {
		return head + ".", nil
	}
	body, err := k.mangleBody(r)
	if err != nil {
		return "", err
	}
	return head + " :- " + body + ".", nil
}

func (k *knowledge) patterns() []pattern {
	positions := map[string]map[int]bool{}
	mark := func(pred string, i int, blank string) bool {
		if baseName(blank) != "fact pattern" || positions[pred][i] {
			return false
		}
		if positions[pred] == nil {
			positions[pred] = map[int]bool{}
		}
		positions[pred][i] = true
		return true
	}
	for _, r := range k.rules {
		for _, a := range r.atoms() {
			for i, t := range a.args {
				if t.blank != "" {
					mark(a.pred, i, t.blank)
				}
			}
		}
	}
	found := map[string]bool{}
	var out []pattern
	for changed := true; changed; {
		changed = false
		for _, r := range k.rules {
			for _, a := range r.atoms() {
				for i, t := range a.args {
					if t.blank != "" || t.val.number || !positions[a.pred][i] || found[t.val.s] {
						continue
					}
					found[t.val.s] = true
					p, err := readPattern(t.val.s)
					if err != nil {
						k.problem(r.where() + ": " + err.Error())
						continue
					}
					out = append(out, p)
					for j, slot := range p.slots {
						if mark(p.pred, j, slot) {
							changed = true
						}
					}
				}
			}
		}
	}
	return out
}

func (k *knowledge) madeFacts() []fact {
	var out []fact
	seen := map[string]bool{}
	add := func(pred string, args ...value) {
		f := fact{pred: pred, args: args}
		if seen[f.key()] {
			return
		}
		seen[f.key()] = true
		if _, ok := k.order[f.key()]; !ok {
			k.order[f.key()] = madeOrder + len(k.order)
		}
		out = append(out, f)
	}
	if k.change {
		add("this run is a change")
	}
	for _, r := range k.rules {
		id := text(r.id)
		add("has a rule for", text(r.file), text(r.head.pred))
		add("defines", id, text(r.head.pred))
		for _, c := range r.conds {
			add("refers to", id, text(c.atom.pred))
		}
		for _, b := range r.blanks() {
			add("has the blank", id, text(b))
		}
		if r.head.pred == "breaks" && len(r.head.args) == 2 && r.head.args[1].blank == "" {
			add("lays down", id, r.head.args[1].val)
		}
		if r.misread {
			add("misread", id)
		}
	}
	for _, p := range k.patterns() {
		add("names", text(p.text), text(p.pred))
		for _, slot := range p.slots {
			add("has the slot", text(p.text), text(slot))
		}
	}
	for _, f := range k.returned {
		add(f.pred, f.args...)
	}
	return out
}

func (k *knowledge) program(reasons map[string]bool) string {
	k.readTemplates()
	var lines []string
	defined := map[string]bool{}
	wanted := map[string]int{}
	k.plain = map[string]string{}
	sym := func(a atom) string {
		k.plain[mangleName(a.pred)] = a.pred
		return mangleName(a.pred) + "/" + strconv.Itoa(len(a.args))
	}
	for _, r := range k.rules {
		clause, err := k.mangleRule(r)
		if err != nil {
			k.problem(r.where() + ": " + err.Error())
			continue
		}
		lines = append(lines, clause)
		defined[sym(r.head)] = true
		for _, c := range r.conds {
			if _, ok := k.templates[c.atom.pred]; !ok {
				wanted[sym(c.atom)] = len(c.atom.args)
			}
		}
	}
	for _, f := range k.madeFacts() {
		lines = append(lines, mangleAtom(f.atom())+".")
		defined[sym(f.atom())] = true
	}
	k.aux = map[*rule]reasonRule{}
	for i, r := range k.rules {
		if !reasons[r.head.pred] || len(r.conds) == 0 {
			continue
		}
		body, err := k.mangleBody(r)
		if err != nil {
			continue
		}
		aux := reasonRule{rule: r, name: fmt.Sprintf("reason__%d", i)}
		inHead := map[string]bool{}
		var args []string
		for _, t := range r.head.args {
			args = append(args, mangleTerm(t))
			inHead[t.blank] = true
		}
		for _, b := range r.blanks() {
			if !inHead[b] {
				aux.vars = append(aux.vars, b)
				args = append(args, mangleVar(b))
			}
		}
		k.aux[r] = aux
		lines = append(lines, aux.name+"("+strings.Join(args, ", ")+") :- "+body+".")
	}
	var decls []string
	for s, arity := range wanted {
		if defined[s] {
			continue
		}
		vars := make([]string, arity)
		for i := range vars {
			vars[i] = "X" + strconv.Itoa(i)
		}
		decls = append(decls, "Decl "+s[:strings.LastIndexByte(s, '/')]+"("+strings.Join(vars, ", ")+").")
	}
	sort.Strings(decls)
	return strings.Join(append(decls, lines...), "\n") + "\n"
}

func fromMangle(t ast.BaseTerm) value {
	c, ok := t.(ast.Constant)
	switch {
	case ok && c.Type == ast.NumberType:
		return count(c.NumValue)
	case ok && c.Type == ast.StringType:
		return text(c.Symbol)
	}
	return text(t.String())
}

func (k *knowledge) evaluate(reasons map[string]bool) bool {
	source := k.program(reasons)
	if len(k.problems) > 0 {
		return false
	}
	unit, err := parse.Unit(strings.NewReader(source))
	if err != nil {
		k.problem("mangle cannot parse what engine.go wrote: " + err.Error())
		return false
	}
	info, err := analysis.AnalyzeOneUnit(unit, nil)
	if err != nil {
		k.problem("mangle cannot accept what engine.go wrote: " + err.Error())
		return false
	}
	store := factstore.NewSimpleInMemoryStore()
	if err := engine.EvalProgram(info, store); err != nil {
		k.problem("mangle cannot evaluate what engine.go wrote: " + err.Error())
		return false
	}
	plain := k.plain
	k.known = map[string][]fact{}
	k.auxFacts = map[string][]fact{}
	for _, s := range store.ListPredicates() {
		pred, ok := plain[s.Symbol]
		target := k.known
		if !ok {
			pred, target = s.Symbol, k.auxFacts
		}
		store.GetFacts(ast.NewQuery(s), func(a ast.Atom) error {
			f := fact{pred: pred}
			for _, arg := range a.Args {
				f.args = append(f.args, fromMangle(arg))
			}
			target[pred] = append(target[pred], f)
			return nil
		})
	}
	for _, group := range []map[string][]fact{k.known, k.auxFacts} {
		for _, facts := range group {
			k.sortFacts(facts)
		}
	}
	k.evaluated = true
	return true
}

func (k *knowledge) sortFacts(facts []fact) {
	place := func(f fact) int {
		if n, ok := k.order[f.key()]; ok {
			return n
		}
		return derivedOrder
	}
	sort.SliceStable(facts, func(i, j int) bool {
		a, b := place(facts[i]), place(facts[j])
		if a != b {
			return a < b
		}
		return showFact(facts[i]) < showFact(facts[j])
	})
}

func (k *knowledge) loadMore() bool {
	more := false
	for _, f := range k.facts("loads") {
		if len(f.args) == 2 && f.args[0] == text(self) && !f.args[1].number && !k.loaded[f.args[1].s] {
			k.load(f.args[1].s)
			more = true
		}
	}
	return more
}

func (k *knowledge) runCommands() bool {
	type job struct {
		command value
		name    string
		input   value
		use     tool
		found   []found
		err     error
	}
	var jobs []*job
	for _, f := range k.facts("uses") {
		if len(f.args) != 3 || k.ran[f.key()] {
			continue
		}
		k.ran[f.key()] = true
		use, ok := toolbox[f.args[1].String()]
		if !ok || f.args[1].number {
			continue
		}
		jobs = append(jobs, &job{command: f.args[0], name: f.args[1].s, input: f.args[2], use: use})
	}
	if len(jobs) == 0 {
		return false
	}
	var wait sync.WaitGroup
	slots := make(chan struct{}, runtime.NumCPU())
	for _, j := range jobs {
		wait.Add(1)
		go func(j *job) {
			defer wait.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			j.found, j.err = j.use(j.input, k)
		}(j)
	}
	wait.Wait()
	for _, j := range jobs {
		if j.err != nil {
			k.problem(fmt.Sprintf("%s could not use %s on %s: %v", j.command, j.name, j.input, j.err))
			continue
		}
		for _, r := range j.found {
			k.returned = append(k.returned, fact{pred: "returned", args: []value{j.command, text(r.field), r.value}})
		}
	}
	return true
}

func (k *knowledge) views() []string {
	var views []string
	for _, f := range k.facts("prints") {
		if len(f.args) == 2 && f.args[0] == text(self) {
			views = append(views, f.args[1].String())
		}
	}
	for _, f := range k.facts("prints in") {
		if len(f.args) == 2 && f.args[0] == text(self) && f.args[1] != text("plain language") {
			k.problem(fmt.Sprintf("engine.go cannot print in %s", f.args[1]))
		}
	}
	for _, f := range k.facts("prints to") {
		if len(f.args) == 2 && f.args[0] == text(self) && f.args[1] != text("standard output") {
			k.problem(fmt.Sprintf("engine.go cannot print to %s", f.args[1]))
		}
	}
	return views
}

func (k *knowledge) reasonPatterns(views []string) []pattern {
	var out []pattern
	for _, view := range views {
		for _, f := range k.facts("gives reasons for") {
			if len(f.args) != 2 || f.args[0] != text(view) {
				continue
			}
			p, err := readPattern(f.args[1].String())
			if err != nil {
				k.problem(err.Error())
				continue
			}
			out = append(out, p)
		}
	}
	return out
}

func (k *knowledge) why(f fact) []string {
	for _, r := range k.rules {
		if r.head.pred != f.pred || len(r.head.args) != len(f.args) {
			continue
		}
		if len(r.conds) == 0 {
			if len(r.blanks()) == 0 && showFact(f) == showAtom(r.head) {
				return []string{r.file + " says so"}
			}
			continue
		}
		aux, ok := k.aux[r]
		if !ok {
			continue
		}
		for _, a := range k.auxFacts[aux.name] {
			head := fact{pred: f.pred, args: a.args[:min(len(f.args), len(a.args))]}
			if len(a.args) != len(f.args)+len(aux.vars) || head.key() != f.key() {
				continue
			}
			binding := map[string]value{}
			for i, t := range r.head.args {
				if t.blank != "" {
					binding[t.blank] = a.args[i]
				}
			}
			for i, v := range aux.vars {
				binding[v] = a.args[len(f.args)+i]
			}
			var out []string
			for _, c := range r.conds {
				ground := atom{pred: c.atom.pred}
				for _, t := range c.atom.args {
					if t.blank != "" {
						t = term{val: binding[t.blank]}
					}
					ground.args = append(ground.args, t)
				}
				reason := showAtom(ground)
				if c.negated {
					reason = "not " + reason
				}
				out = append(out, reason)
			}
			return out
		}
	}
	return nil
}

func (k *knowledge) giveReasons(patterns []pattern) {
	k.extra["holds because"] = nil
	for _, p := range patterns {
		for _, f := range k.facts(p.pred) {
			if len(f.args) != len(p.slots) {
				continue
			}
			for _, reason := range k.why(f) {
				k.extra["holds because"] = append(k.extra["holds because"], fact{pred: "holds because", args: []value{text(showFact(f)), text(reason)}})
			}
		}
	}
}

func (k *knowledge) code(answer value) (int, bool) {
	for _, f := range k.facts("exits with") {
		if len(f.args) == 2 && f.args[0] == answer && f.args[1].number {
			return int(f.args[1].n), true
		}
	}
	return 0, false
}

func (k *knowledge) answer() int {
	var answers []value
	for _, f := range k.facts("conforms") {
		if len(f.args) == 2 && !contains(answers, f.args[1]) {
			answers = append(answers, f.args[1])
		}
	}
	if len(answers) != 1 {
		k.problem(fmt.Sprintf("the folder has %d answers, but it needs one", len(answers)))
		return brokenCode
	}
	code, ok := k.code(answers[0])
	if !ok {
		k.problem(fmt.Sprintf("nothing says what %s exits with", answers[0]))
	}
	return code
}

func contains(values []value, v value) bool {
	for _, w := range values {
		if w == v {
			return true
		}
	}
	return false
}

func (k *knowledge) show(view string) []string {
	var out []string
	inView := map[string]bool{}
	for _, f := range k.facts("in " + view) {
		if len(f.args) == 1 {
			inView[f.args[0].String()] = true
		}
	}
	last := ""
	for _, r := range k.rules {
		if !inView[r.id] {
			continue
		}
		if len(out) > 0 && (r.gap || r.file != last) {
			out = append(out, "")
		}
		out = append(out, showAtom(r.head))
		for i, c := range r.conds {
			out = append(out, showCondition(i, c))
		}
		last = r.file
	}
	shown := map[string]bool{}
	for _, f := range k.facts("shows") {
		if len(f.args) != 2 || f.args[0] != text(view) || shown[f.args[1].String()] {
			continue
		}
		shown[f.args[1].String()] = true
		p, err := readPattern(f.args[1].String())
		if err != nil {
			k.problem(err.Error())
			continue
		}
		var lines []string
		for _, g := range k.all(p.pred) {
			if len(g.args) == len(p.slots) {
				lines = append(lines, showFact(g))
			}
		}
		if len(lines) > 0 && len(out) > 0 {
			out = append(out, "")
		}
		out = append(out, lines...)
	}
	return out
}

func (k *knowledge) fail() {
	w := bufio.NewWriter(os.Stdout)
	for _, p := range k.problems {
		fmt.Fprintln(w, showFact(fact{pred: "a problem", args: []value{text(p)}}))
	}
	w.Flush()
	code := brokenCode
	if c, ok := k.code(text("broken")); ok && k.evaluated {
		code = c
	}
	os.Exit(code)
}

func main() {
	root := "spec.plain"
	if len(os.Args) > 1 {
		root = os.Args[1]
	}
	k := newKnowledge()
	k.load(root)
	for round := 0; ; round++ {
		if round > 100 {
			k.problem("the commands never settle")
		}
		if len(k.problems) > 0 || !k.evaluate(nil) {
			k.fail()
		}
		if k.loadMore() || k.runCommands() {
			continue
		}
		break
	}
	views := k.views()
	patterns := k.reasonPatterns(views)
	reasons := map[string]bool{}
	for _, p := range patterns {
		reasons[p.pred] = true
	}
	if len(k.problems) > 0 || !k.evaluate(reasons) {
		k.fail()
	}
	k.giveReasons(patterns)
	code := k.answer()
	var lines []string
	for _, view := range views {
		lines = append(lines, k.show(view)...)
	}
	if len(k.problems) > 0 {
		k.fail()
	}
	w := bufio.NewWriter(os.Stdout)
	for _, line := range lines {
		fmt.Fprintln(w, line)
	}
	w.Flush()
	os.Exit(code)
}
