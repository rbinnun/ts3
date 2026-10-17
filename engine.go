package main

import (
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
)

const (
	self       = "engine.go"
	indent     = "    "
	roundLimit = 64
	factLimit  = 1000000
)

var (
	variableText = regexp.MustCompile(`^\[([a-z][a-z0-9]*(?: [a-z0-9]+)*)\]$`)
	numberText   = regexp.MustCompile(`^-?[0-9]+$`)
	phraseText   = regexp.MustCompile(`^[a-z0-9]+(?: [a-z0-9]+)*$`)
	patternPart  = regexp.MustCompile(`\[[a-z][a-z0-9]*(?: [a-z0-9]+)*\]|[a-z0-9]+`)
)

type termKind int

const (
	stringTerm termKind = iota
	numberTerm
	variableTerm
)

type term struct {
	kind  termKind
	text  string
	value int64
}

func str(text string) term      { return term{kind: stringTerm, text: text} }
func num(value int64) term      { return term{kind: numberTerm, value: value} }
func variable(name string) term { return term{kind: variableTerm, text: name} }

func textOf(t term) string {
	if t.kind == numberTerm {
		return strconv.FormatInt(t.value, 10)
	}
	return t.text
}

type shape int

const (
	relationShape shape = iota
	isShape
	sentenceShape
)

type literal struct {
	negated bool
	shape   shape
	word    string
	args    []term
}

func relation(word string, args ...term) literal {
	return literal{shape: relationShape, word: word, args: args}
}

func isFact(word string, subject term) literal {
	return literal{shape: isShape, word: word, args: []term{subject}}
}

func (l literal) key() string {
	return fmt.Sprintf("%d %d %s", l.shape, len(l.args), l.word)
}

func (l literal) ground() bool {
	for _, a := range l.args {
		if a.kind == variableTerm {
			return false
		}
	}
	return true
}

type rule struct {
	id    string
	file  string
	first int
	last  int
	head  literal
	body  []literal
}

type source struct {
	name     string
	rules    []rule
	misread  []string
	problems []string
}

type field struct {
	text   string
	quoted bool
}

func splitFields(line string) ([]field, error) {
	var fields []field
	rest := line
	for {
		var f field
		if rest != "" && (rest[0] == '"' || rest[0] == '\'') {
			end := -1
			for i := 1; i < len(rest); i++ {
				if rest[i] == rest[0] && (i+1 == len(rest) || strings.HasPrefix(rest[i+1:], ", ")) {
					end = i
					break
				}
			}
			if end < 0 {
				return nil, fmt.Errorf("a quote is never closed")
			}
			f = field{text: rest[1:end], quoted: true}
			rest = rest[end+1:]
		} else {
			cut := strings.Index(rest, ", ")
			if cut < 0 {
				cut = len(rest)
			}
			f = field{text: rest[:cut]}
			rest = rest[cut:]
		}
		fields = append(fields, f)
		if rest == "" {
			return fields, nil
		}
		rest = rest[2:]
	}
}

func termOf(f field) term {
	if f.quoted {
		return str(f.text)
	}
	if m := variableText.FindStringSubmatch(f.text); m != nil {
		return variable(m[1])
	}
	if numberText.MatchString(f.text) {
		if n, err := strconv.ParseInt(f.text, 10, 64); err == nil {
			return num(n)
		}
	}
	return str(f.text)
}

func readLiteral(line string) (literal, error) {
	fields, err := splitFields(line)
	if err != nil {
		return literal{}, err
	}
	switch len(fields) {
	case 1:
		if fields[0].quoted || !phraseText.MatchString(fields[0].text) {
			return literal{}, fmt.Errorf("a line of one part must be plain words")
		}
		return literal{shape: sentenceShape, word: fields[0].text}, nil
	case 2:
		return literal{}, fmt.Errorf("a line needs something, a verb and what it is about")
	}
	verb := fields[1]
	if verb.quoted || !phraseText.MatchString(verb.text) {
		return literal{}, fmt.Errorf("the verb must be plain words")
	}
	if verb.text == "is" {
		object := fields[2]
		if len(fields) != 3 || object.quoted || !phraseText.MatchString(object.text) {
			return literal{}, fmt.Errorf("what something is must be plain words")
		}
		return isFact(object.text, termOf(fields[0])), nil
	}
	args := []term{termOf(fields[0])}
	for _, f := range fields[2:] {
		args = append(args, termOf(f))
	}
	return relation(verb.text, args...), nil
}

var conditionLeads = []struct {
	lead    string
	negated bool
}{{"if not ", true}, {"and not ", true}, {"if ", false}, {"and ", false}}

func readCondition(line string) (literal, error) {
	text := strings.TrimLeft(line, " \t")
	for _, c := range conditionLeads {
		if strings.HasPrefix(text, c.lead) {
			l, err := readLiteral(text[len(c.lead):])
			l.negated = c.negated
			return l, err
		}
	}
	return literal{}, fmt.Errorf("an indented line must start with if or and")
}

func plainSafe(s string) bool {
	return s != "" && s == strings.TrimSpace(s) && !strings.Contains(s, ", ") &&
		s[0] != '"' && s[0] != '\'' && !strings.ContainsAny(s, "\r\n") &&
		!variableText.MatchString(s) && !numberText.MatchString(s)
}

func renderTerm(t term) string {
	switch t.kind {
	case variableTerm:
		return "[" + t.text + "]"
	case numberTerm:
		return strconv.FormatInt(t.value, 10)
	}
	s := t.text
	switch {
	case plainSafe(s):
		return s
	case !strings.Contains(s, `"`):
		return `"` + s + `"`
	case !strings.Contains(s, `', `):
		return "'" + s + "'"
	}
	return `"` + s + `"`
}

func renderLiteral(l literal) string {
	switch l.shape {
	case sentenceShape:
		return l.word
	case isShape:
		return renderTerm(l.args[0]) + ", is, " + l.word
	}
	parts := []string{renderTerm(l.args[0]), l.word}
	for _, a := range l.args[1:] {
		parts = append(parts, renderTerm(a))
	}
	return strings.Join(parts, ", ")
}

func conditionLine(l literal, first bool) string {
	lead := indent + "and "
	if first {
		lead = indent + "if "
	}
	if l.negated {
		lead += "not "
	}
	return lead + renderLiteral(l)
}

func ruleLines(r rule) []string {
	lines := []string{renderLiteral(r.head)}
	for i, b := range r.body {
		lines = append(lines, conditionLine(b, i == 0))
	}
	return lines
}

func read(name string, lines []string) source {
	s := source{name: name}
	var current *rule
	skipping := false
	finish := func() {
		if current != nil {
			if len(current.body) == 0 && !current.head.ground() {
				s.problems = append(s.problems, current.id+" states a fact that holds a variable")
			} else {
				s.rules = append(s.rules, *current)
			}
		}
		current = nil
	}
	unreadable := func(id string, err error) {
		s.problems = append(s.problems, fmt.Sprintf("%s cannot be read: %v", id, err))
		s.misread = append(s.misread, id)
		current = nil
		skipping = true
	}
	for i, line := range lines {
		id := fmt.Sprintf("%s line %d", name, i+1)
		switch {
		case strings.TrimSpace(line) == "":
			finish()
			skipping = false
			if line != "" {
				s.misread = append(s.misread, id)
			}
		case line[0] == ' ' || line[0] == '\t':
			if skipping {
				continue
			}
			if current == nil {
				unreadable(id, fmt.Errorf("it is indented but follows no rule"))
				continue
			}
			l, err := readCondition(line)
			if err != nil {
				unreadable(id, err)
				continue
			}
			current.body = append(current.body, l)
			current.last = i + 1
			if conditionLine(l, len(current.body) == 1) != line {
				s.misread = append(s.misread, id)
			}
		default:
			finish()
			skipping = false
			l, err := readLiteral(line)
			if err != nil {
				unreadable(id, err)
				continue
			}
			current = &rule{id: id, file: name, first: i + 1, last: i + 1, head: l}
			if renderLiteral(l) != line {
				s.misread = append(s.misread, id)
			}
		}
	}
	finish()
	return s
}

func readPattern(text string) (literal, bool) {
	parts := patternPart.FindAllString(text, -1)
	if len(parts) < 2 || strings.Join(parts, " ") != text || parts[0][0] != '[' {
		return literal{}, false
	}
	var words []string
	i := 1
	for ; i < len(parts) && parts[i][0] != '['; i++ {
		words = append(words, parts[i])
	}
	args := []term{variable(strings.Trim(parts[0], "[]"))}
	for ; i < len(parts); i++ {
		if parts[i][0] != '[' {
			return literal{}, false
		}
		args = append(args, variable(strings.Trim(parts[i], "[]")))
	}
	if len(words) == 0 {
		return literal{}, false
	}
	if len(args) == 1 {
		if len(words) < 2 || words[0] != "is" {
			return literal{}, false
		}
		return isFact(strings.Join(words[1:], " "), args[0]), true
	}
	return relation(strings.Join(words, " "), args...), true
}

type piece struct {
	text string
	slot int
}

type template []piece

func (t template) apply(args []string) string {
	var b strings.Builder
	for _, p := range t {
		if p.slot >= 0 {
			b.WriteString(args[p.slot])
		} else {
			b.WriteString(p.text)
		}
	}
	return b.String()
}

func defaultTemplate(l literal) template {
	t := template{{text: strings.ReplaceAll(l.word, " ", "_") + "(", slot: -1}}
	for i := range l.args {
		if i > 0 {
			t = append(t, piece{text: ", ", slot: -1})
		}
		t = append(t, piece{slot: i})
	}
	return append(t, piece{text: ")", slot: -1})
}

func mangleTerm(t term) string {
	switch t.kind {
	case variableTerm:
		words := strings.Fields(t.text)
		for i, w := range words {
			words[i] = strings.ToUpper(w[:1]) + w[1:]
		}
		return strings.Join(words, "")
	case numberTerm:
		return ast.Number(t.value).String()
	}
	return ast.String(t.text).String()
}

func identifierByte(c byte) bool {
	return c == '_' || c == ':' || c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

func mangleTokens(text string) []string {
	var tokens []string
	for i := 0; i < len(text); {
		j := i + 1
		switch {
		case text[i] == '"':
			for j < len(text) && text[j] != '"' {
				if text[j] == '\\' {
					j++
				}
				j++
			}
			j++
		case identifierByte(text[i]):
			for j < len(text) && identifierByte(text[j]) {
				j++
			}
		}
		if j > len(text) {
			j = len(text)
		}
		tokens = append(tokens, text[i:j])
		i = j
	}
	return tokens
}

func learnTemplate(plain, mangle string) (literal, template, error) {
	l, err := readLiteral(plain)
	if err != nil {
		return l, nil, err
	}
	text := strings.TrimSuffix(strings.TrimSpace(mangle), ".")
	rendered := make([]string, len(l.args))
	for i, a := range l.args {
		rendered[i] = mangleTerm(a)
	}
	var t template
	seen := make([]int, len(l.args))
	for _, token := range mangleTokens(text) {
		slot := -1
		for i, r := range rendered {
			if r == token {
				seen[i]++
				if slot < 0 {
					slot = i
				}
			}
		}
		if slot >= 0 {
			t = append(t, piece{slot: slot})
		} else {
			t = append(t, piece{text: token, slot: -1})
		}
	}
	for i, n := range seen {
		if n != 1 {
			return l, nil, fmt.Errorf("the mangle must name %s exactly once", renderTerm(l.args[i]))
		}
	}
	if t.apply(rendered) != text {
		return l, nil, fmt.Errorf("the mangle cannot be taken apart")
	}
	return l, t, nil
}

type lookup struct {
	sym ast.PredicateSym
	ok  bool
}

type translator struct {
	templates  map[string]template
	mu         sync.Mutex
	predicates map[string]lookup
}

func (tr *translator) template(l literal) template {
	if t, ok := tr.templates[l.key()]; ok {
		return t
	}
	return defaultTemplate(l)
}

func (tr *translator) literal(l literal) string {
	args := make([]string, len(l.args))
	for i, a := range l.args {
		args[i] = mangleTerm(a)
	}
	text := tr.template(l).apply(args)
	if l.negated {
		return "!" + text
	}
	return text
}

func (tr *translator) clause(head literal, body []literal) string {
	text := tr.literal(head)
	if len(body) > 0 {
		conditions := make([]string, len(body))
		for i, b := range body {
			conditions[i] = tr.literal(b)
		}
		text += " :- " + strings.Join(conditions, ", ")
	}
	return text + "."
}

func (tr *translator) predicate(l literal) (ast.PredicateSym, bool) {
	tr.mu.Lock()
	defer tr.mu.Unlock()
	if found, ok := tr.predicates[l.key()]; ok {
		return found.sym, found.ok
	}
	found := tr.find(l)
	tr.predicates[l.key()] = found
	return found.sym, found.ok
}

func (tr *translator) find(l literal) lookup {
	names := make([]string, len(l.args))
	for i := range names {
		names[i] = fmt.Sprintf("V%d", i)
	}
	a, err := parse.Atom(tr.template(l).apply(names))
	if err != nil || a.Predicate.IsBuiltin() || strings.Contains(a.Predicate.Symbol, ":") || len(a.Args) != len(names) {
		return lookup{}
	}
	for i, arg := range a.Args {
		if v, ok := arg.(ast.Variable); !ok || v.Symbol != names[i] {
			return lookup{}
		}
	}
	return lookup{sym: a.Predicate, ok: true}
}

type clause struct {
	origin string
	text   string
}

type knowledge struct {
	m     *machine
	store factstore.FactStore
}

func termOfConstant(b ast.BaseTerm) term {
	c, ok := b.(ast.Constant)
	if !ok {
		return str(b.String())
	}
	switch c.Type {
	case ast.StringType:
		return str(c.Symbol)
	case ast.NumberType:
		return num(c.NumValue)
	}
	return str(c.String())
}

func (k *knowledge) facts(l literal) [][]term {
	if k == nil {
		return nil
	}
	sym, ok := k.m.tr.predicate(l)
	if !ok {
		return nil
	}
	var rows [][]term
	k.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
		row := make([]term, len(a.Args))
		for i, arg := range a.Args {
			row[i] = termOfConstant(arg)
		}
		rows = append(rows, row)
		return nil
	})
	return rows
}

func (k *knowledge) ask(who, pattern string) [][]term {
	k.m.record(who, pattern)
	l, ok := readPattern(pattern)
	if !ok {
		return nil
	}
	return k.facts(l)
}

func (k *knowledge) lines(l literal) []string {
	seen := map[string]bool{}
	var lines []string
	for _, row := range k.facts(l) {
		line := renderLiteral(literal{shape: l.shape, word: l.word, args: row})
		if !seen[line] {
			seen[line] = true
			lines = append(lines, line)
		}
	}
	sort.Slice(lines, func(i, j int) bool { return naturalLess(lines[i], lines[j]) })
	return lines
}

func digitRun(s string, i int) int {
	j := i
	for j < len(s) && s[j] >= '0' && s[j] <= '9' {
		j++
	}
	return j
}

func naturalLess(a, b string) bool {
	i, j := 0, 0
	for i < len(a) && j < len(b) {
		ai, bj := digitRun(a, i), digitRun(b, j)
		if ai > i && bj > j {
			x, y := strings.TrimLeft(a[i:ai], "0"), strings.TrimLeft(b[j:bj], "0")
			if len(x) != len(y) {
				return len(x) < len(y)
			}
			if x != y {
				return x < y
			}
			i, j = ai, bj
			continue
		}
		if a[i] != b[j] {
			return a[i] < b[j]
		}
		i++
		j++
	}
	return len(a)-i < len(b)-j
}

type machine struct {
	kind     string
	sources  []source
	tried    map[string]bool
	tr       *translator
	creators map[string]map[string]bool
	created  []literal
	shapes   map[string][]literal
	mu       sync.Mutex
	problems []string
	known    map[string]bool
	asked    map[[2]string]bool
}

func newMachine(kind string) *machine {
	return &machine{
		kind:     kind,
		tried:    map[string]bool{},
		tr:       &translator{templates: map[string]template{}, predicates: map[string]lookup{}},
		creators: map[string]map[string]bool{},
		shapes:   map[string][]literal{},
		known:    map[string]bool{},
		asked:    map[[2]string]bool{},
	}
}

func (m *machine) problem(text string) {
	text = strings.Join(strings.Fields(strings.ReplaceAll(text, `"`, "'")), " ")
	m.mu.Lock()
	defer m.mu.Unlock()
	if !m.known[text] {
		m.known[text] = true
		m.problems = append(m.problems, text)
	}
}

func (m *machine) record(who, pattern string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.asked[[2]string{who, pattern}] = true
}

func (m *machine) ground(pattern string) [][]term {
	m.record(self, pattern)
	want, ok := readPattern(pattern)
	if !ok {
		return nil
	}
	var rows [][]term
	for _, s := range m.sources {
		for _, r := range s.rules {
			if len(r.body) == 0 && r.head.key() == want.key() && r.head.ground() {
				rows = append(rows, r.head.args)
			}
		}
	}
	return rows
}

func (m *machine) load(name string) {
	m.tried[name] = true
	data, err := os.ReadFile(name)
	if os.IsNotExist(err) {
		return
	}
	if err != nil {
		m.problem(fmt.Sprintf("%s cannot be opened: %v", name, err))
		return
	}
	text := strings.TrimSuffix(string(data), "\n")
	var lines []string
	if len(data) > 0 {
		lines = strings.Split(text, "\n")
	}
	s := read(name, lines)
	for _, p := range s.problems {
		m.problem(p)
	}
	m.sources = append(m.sources, s)
}

func (m *machine) loadAll(start string) {
	m.load(start)
	for more := true; more; {
		more = false
		for _, f := range m.ground("[go file] loads [plain file]") {
			if f[0] == str(self) && f[1].kind == stringTerm && !m.tried[f[1].text] {
				m.load(f[1].text)
				more = true
			}
		}
	}
}

func (m *machine) learnMeanings() {
	for _, f := range m.ground("[plain] means in mangle [mangle]") {
		if f[0].kind != stringTerm || f[1].kind != stringTerm {
			continue
		}
		l, t, err := learnTemplate(f[0].text, f[1].text)
		if err != nil {
			m.problem(fmt.Sprintf("the meaning of %s cannot be learned: %v", f[0].text, err))
			continue
		}
		if old, ok := m.tr.templates[l.key()]; ok && !sameTemplate(old, t, len(l.args)) {
			m.problem(fmt.Sprintf("%s is given two meanings in mangle", f[0].text))
			continue
		}
		m.tr.templates[l.key()] = t
	}
}

func sameTemplate(a, b template, arity int) bool {
	names := make([]string, arity)
	for i := range names {
		names[i] = fmt.Sprintf("V%d", i)
	}
	return a.apply(names) == b.apply(names)
}

func (m *machine) learnCreators() {
	for _, f := range m.ground("[file] creates fact [fact pattern]") {
		l, ok := readPattern(f[1].text)
		if !ok {
			m.problem(fmt.Sprintf("%s is not a fact pattern", f[1].text))
			continue
		}
		if m.creators[l.key()] == nil {
			m.creators[l.key()] = map[string]bool{}
			m.created = append(m.created, l)
		}
		m.creators[l.key()][f[0].text] = true
	}
}

func (m *machine) learnShapes() {
	seen := map[string]bool{}
	add := func(l literal) {
		if _, ok := m.tr.predicate(l); ok && !seen[l.key()] {
			seen[l.key()] = true
			m.shapes[l.word] = append(m.shapes[l.word], l)
		}
	}
	for _, l := range m.created {
		add(l)
	}
	for _, s := range m.sources {
		for _, r := range s.rules {
			add(r.head)
			for _, b := range r.body {
				add(b)
			}
		}
	}
}

func (m *machine) mayCreate(who string, l literal) bool {
	return m.creators[l.key()][who]
}

func (m *machine) engineFacts() []literal {
	var facts []literal
	add := func(l literal) {
		if m.mayCreate(self, l) {
			facts = append(facts, l)
		}
	}
	if m.kind != "" {
		add(isFact("the kind of this run", str(m.kind)))
	}
	m.mu.Lock()
	for _, p := range m.problems {
		add(isFact("a problem", str(p)))
	}
	m.mu.Unlock()
	for _, s := range m.sources {
		for _, id := range s.misread {
			add(isFact("misread", str(id)))
		}
		for _, r := range s.rules {
			id := str(r.id)
			add(relation("is in", id, str(s.name)))
			add(relation("defines", id, str(r.head.word)))
			if r.head.shape == relationShape && r.head.word == "breaks" && len(r.head.args) == 2 && r.head.args[1].kind == stringTerm {
				add(relation("lays down", id, r.head.args[1]))
			}
			for _, b := range r.body {
				if _, ok := m.tr.predicate(b); ok {
					add(relation("refers to", id, str(b.word)))
				}
			}
			for _, l := range append([]literal{r.head}, r.body...) {
				for _, a := range l.args {
					if a.kind != stringTerm {
						continue
					}
					if p, ok := readPattern(a.text); ok {
						add(relation("names", a, str(p.word)))
					}
				}
			}
		}
	}
	return facts
}

func (m *machine) returned(commands map[term]map[call]bool, results map[call][]result) []literal {
	var facts []literal
	for command, calls := range commands {
		for c := range calls {
			for _, r := range results[c] {
				if l := r.fact(command); m.mayCreate(tools, l) {
					facts = append(facts, l)
				}
			}
		}
	}
	return facts
}

func (m *machine) ruleClauses(sources []source, factsOnly bool) []clause {
	var clauses []clause
	for _, s := range sources {
		for _, r := range s.rules {
			if factsOnly && len(r.body) > 0 {
				continue
			}
			clauses = append(clauses, clause{origin: r.id, text: m.tr.clause(r.head, r.body)})
		}
	}
	return clauses
}

func (m *machine) factClauses(origin string, facts []literal) []clause {
	clauses := make([]clause, len(facts))
	for i, f := range facts {
		clauses[i] = clause{origin: origin, text: m.tr.clause(f, nil)}
	}
	return clauses
}

func joinClauses(clauses []clause) string {
	texts := make([]string, len(clauses))
	for i, c := range clauses {
		texts[i] = c.text
	}
	return strings.Join(texts, "\n")
}

func (m *machine) parseUnit(clauses []clause) (parse.SourceUnit, error) {
	unit, err := parse.Unit(strings.NewReader(joinClauses(clauses)))
	if err == nil {
		return unit, nil
	}
	var good []clause
	for _, c := range clauses {
		if _, cerr := parse.Clause(c.text); cerr != nil {
			m.problem(fmt.Sprintf("%s cannot be put into mangle: %v", c.origin, cerr))
		} else {
			good = append(good, c)
		}
	}
	if len(good) == len(clauses) {
		return unit, err
	}
	return parse.Unit(strings.NewReader(joinClauses(good)))
}

func (m *machine) evaluate(clauses []clause) (*knowledge, error) {
	unit, err := m.parseUnit(clauses)
	if err != nil {
		return nil, err
	}
	defined := map[ast.PredicateSym]bool{}
	for _, c := range unit.Clauses {
		defined[c.Head.Predicate] = true
	}
	extra := map[ast.PredicateSym]ast.Decl{}
	for _, l := range m.created {
		if sym, ok := m.tr.predicate(l); ok && !defined[sym] {
			extra[sym] = ast.NewSyntheticDeclFromSym(sym)
		}
	}
	info, err := analysis.AnalyzeOneUnit(unit, extra)
	if err != nil {
		return nil, err
	}
	store := factstore.NewSimpleInMemoryStore()
	if err := engine.EvalProgram(info, store, engine.WithCreatedFactLimit(factLimit)); err != nil {
		return nil, err
	}
	return &knowledge{m: m, store: store}, nil
}

func sameCommands(a, b map[term]map[call]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for command, calls := range a {
		if len(b[command]) != len(calls) {
			return false
		}
		for c := range calls {
			if !b[command][c] {
				return false
			}
		}
	}
	return true
}

func (m *machine) program(factsOnly bool, commands map[term]map[call]bool, results map[call][]result) []clause {
	clauses := m.ruleClauses(m.sources, factsOnly)
	clauses = append(clauses, m.factClauses(self, m.engineFacts())...)
	return append(clauses, m.factClauses(tools, m.returned(commands, results))...)
}

func (m *machine) settle() *knowledge {
	results := map[call][]result{}
	commands := map[term]map[call]bool{}
	for round := 0; ; round++ {
		k, err := m.evaluate(m.program(false, commands, results))
		if err != nil {
			m.problem(fmt.Sprintf("the rules cannot be evaluated: %v", err))
			k, err = m.evaluate(m.program(true, commands, results))
			if err != nil {
				m.problem(fmt.Sprintf("even the facts cannot be evaluated: %v", err))
				return nil
			}
			return k
		}
		next := map[term]map[call]bool{}
		var pending []call
		for _, f := range k.ask(self, "[command] uses [tool] [input]") {
			c := call{tool: f[1], input: f[2]}
			if next[f[0]] == nil {
				next[f[0]] = map[call]bool{}
			}
			next[f[0]][c] = true
			if _, done := results[c]; !done {
				results[c] = nil
				pending = append(pending, c)
			}
		}
		if len(pending) == 0 && sameCommands(next, commands) {
			return k
		}
		if round == roundLimit {
			m.problem(fmt.Sprintf("the commands did not settle after %d rounds", roundLimit))
			return k
		}
		m.run(pending, k, results)
		commands = next
	}
}

func (m *machine) run(calls []call, k *knowledge, results map[call][]result) {
	var wg sync.WaitGroup
	var mu sync.Mutex
	slots := make(chan struct{}, max(2, runtime.NumCPU()))
	for _, c := range calls {
		wg.Add(1)
		go func(c call) {
			defer wg.Done()
			slots <- struct{}{}
			defer func() { <-slots }()
			found, err := runTool(c, k)
			if err != nil {
				m.problem(fmt.Sprintf("%s on %s failed: %v", textOf(c.tool), textOf(c.input), err))
			}
			mu.Lock()
			results[c] = found
			mu.Unlock()
		}(c)
	}
	wg.Wait()
}

func (m *machine) viewProgram(k *knowledge) []string {
	inView := map[string]bool{}
	for _, f := range k.ask(self, "[rule] is in the knowledge view") {
		inView[f[0].text] = true
	}
	var lines []string
	var previous *rule
	for _, s := range m.sources {
		for i := range s.rules {
			r := &s.rules[i]
			if !inView[r.id] {
				continue
			}
			adjacent := previous != nil && previous.file == r.file && previous.last+1 == r.first
			if len(lines) > 0 && !adjacent {
				lines = append(lines, "")
			}
			lines = append(lines, ruleLines(*r)...)
			previous = r
		}
	}
	var observed []string
	for _, f := range k.ask(self, "[word] is observed") {
		observed = append(observed, f[0].text)
	}
	sort.Strings(observed)
	for _, word := range observed {
		var group []string
		for _, l := range m.shapes[word] {
			group = append(group, k.lines(l)...)
		}
		if len(group) == 0 {
			continue
		}
		if len(lines) > 0 {
			lines = append(lines, "")
		}
		lines = append(lines, group...)
	}
	return lines
}

func (m *machine) position(l literal) int {
	text := renderLiteral(l)
	n := 0
	for _, s := range m.sources {
		for _, r := range s.rules {
			if len(r.body) == 0 && renderLiteral(r.head) == text {
				return n
			}
			n++
		}
	}
	return n
}

func (m *machine) patterns(k *knowledge, instruction, view string) []literal {
	type placed struct {
		at      int
		pattern literal
	}
	var found []placed
	seen := map[string]bool{}
	verb, _ := readPattern(instruction)
	for _, f := range k.ask(self, instruction) {
		if f[0] != str(view) || f[1].kind != stringTerm {
			continue
		}
		l, ok := readPattern(f[1].text)
		if !ok {
			m.problem(fmt.Sprintf("%s is not a fact pattern", f[1].text))
			continue
		}
		if !seen[l.key()] {
			seen[l.key()] = true
			found = append(found, placed{m.position(relation(verb.word, f...)), l})
		}
	}
	sort.SliceStable(found, func(i, j int) bool { return found[i].at < found[j].at })
	patterns := make([]literal, len(found))
	for i, p := range found {
		patterns[i] = p.pattern
	}
	return patterns
}

func (m *machine) reproduce(k *knowledge, view string) {
	s := read(view, m.viewProgram(k))
	for _, p := range s.problems {
		m.problem(p)
	}
	for _, id := range s.misread {
		m.problem(id + " does not read back as written")
	}
	again, err := m.evaluate(m.ruleClauses([]source{s}, false))
	if err != nil {
		m.problem(fmt.Sprintf("%s cannot be evaluated: %v", view, err))
		return
	}
	for _, l := range m.patterns(k, "[view] reproduces [fact pattern]", view) {
		want, got := k.lines(l), again.lines(l)
		wanted, gotten := toSet(want), toSet(got)
		for _, line := range want {
			if !gotten[line] {
				m.problem(fmt.Sprintf("%s does not reproduce: %s", view, line))
			}
		}
		for _, line := range got {
			if !wanted[line] {
				m.problem(fmt.Sprintf("%s reproduces what is not so: %s", view, line))
			}
		}
	}
}

func toSet(lines []string) map[string]bool {
	set := map[string]bool{}
	for _, l := range lines {
		set[l] = true
	}
	return set
}

func (m *machine) checkInstructions(k *knowledge) {
	given := map[string]bool{}
	for _, f := range k.facts(relation("executes instruction", variable("file"), variable("instruction"))) {
		if l, ok := readPattern(f[1].text); ok {
			given[f[0].text+" "+l.key()] = true
		}
	}
	var missing []string
	for a := range m.asked {
		l, ok := readPattern(a[1])
		if !ok || !given[a[0]+" "+l.key()] {
			missing = append(missing, fmt.Sprintf("%s follows an instruction the spec does not give it: %s", a[0], a[1]))
		}
	}
	sort.Strings(missing)
	for _, p := range missing {
		m.problem(p)
	}
}

func (m *machine) answer(k *knowledge) term {
	if len(m.problems) > 0 || len(k.ask(self, "[text] is a problem")) > 0 {
		return str("broken")
	}
	answers := map[term]bool{}
	for _, f := range k.ask(self, "[folder] conforms [answer]") {
		answers[f[1]] = true
	}
	for a := range answers {
		if len(answers) == 1 {
			return a
		}
	}
	m.problem(fmt.Sprintf("the folder conforms %d ways instead of one", len(answers)))
	return str("broken")
}

func (m *machine) exitCode(k *knowledge, answer term) int {
	for _, want := range []term{answer, str("broken")} {
		var codes []int64
		for _, f := range k.ask(self, "[answer] exits with [code]") {
			if f[0] == want && f[1].kind == numberTerm {
				codes = append(codes, f[1].value)
			}
		}
		if len(codes) == 1 {
			return int(codes[0])
		}
		m.problem(fmt.Sprintf("%s exits with %d codes instead of one", textOf(want), len(codes)))
	}
	return 2
}

func (m *machine) addProblems(k *knowledge) {
	for _, p := range m.problems {
		l := isFact("a problem", str(p))
		if !m.mayCreate(self, l) {
			continue
		}
		if a, err := parse.Atom(m.tr.literal(l)); err == nil {
			k.store.Add(a)
		}
	}
}

func (m *machine) render(k *knowledge, view string) string {
	var lines []string
	for _, l := range m.patterns(k, "[view] shows [fact pattern]", view) {
		lines = append(lines, k.lines(l)...)
	}
	program := m.viewProgram(k)
	if len(lines) > 0 && len(program) > 0 {
		lines = append(lines, "")
	}
	lines = append(lines, program...)
	if len(lines) == 0 {
		return ""
	}
	return strings.Join(lines, "\n") + "\n"
}

func (m *machine) confess() {
	var b strings.Builder
	for _, p := range m.problems {
		b.WriteString(renderLiteral(isFact("a problem", str(p))) + "\n")
	}
	os.Stderr.WriteString(b.String())
}

func (m *machine) finish(k *knowledge) int {
	if k == nil {
		m.confess()
		return 2
	}
	var views []string
	for _, f := range k.ask(self, "[go file] prints [view]") {
		if f[0] == str(self) && f[1].kind == stringTerm {
			views = append(views, f[1].text)
		}
	}
	sort.Strings(views)
	plain, standardOutput := false, false
	for _, f := range k.ask(self, "[go file] prints in [language]") {
		if f[0] != str(self) {
			continue
		}
		if f[1] == str("plain language") {
			plain = true
		} else {
			m.problem(fmt.Sprintf("%s cannot print in %s", self, textOf(f[1])))
		}
	}
	for _, f := range k.ask(self, "[go file] prints to [place]") {
		if f[0] != str(self) {
			continue
		}
		if f[1] == str("standard output") {
			standardOutput = true
		} else {
			m.problem(fmt.Sprintf("%s cannot print to %s", self, textOf(f[1])))
		}
	}
	for _, v := range views {
		m.reproduce(k, v)
	}
	m.checkInstructions(k)
	code := m.exitCode(k, m.answer(k))
	m.addProblems(k)
	if !plain || !standardOutput || len(views) == 0 {
		m.confess()
		return code
	}
	var b strings.Builder
	for _, v := range views {
		b.WriteString(m.render(k, v))
	}
	os.Stdout.WriteString(b.String())
	return code
}

func main() {
	start, kind := "spec.plain", ""
	if len(os.Args) > 1 {
		start = os.Args[1]
	}
	if len(os.Args) > 2 {
		kind = os.Args[2]
	}
	m := newMachine(kind)
	m.loadAll(start)
	m.learnMeanings()
	m.learnCreators()
	m.learnShapes()
	os.Exit(m.finish(m.settle()))
}
