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
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode"

	"codeberg.org/TauCeti/mangle-go/analysis"
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"

	_ "modernc.org/sqlite"
)

const (
	selfName     = "engine.go"
	toolsName    = "tools.go"
	entryFile    = "spec.plain"
	changeEnv    = "PLAIN_THIS_RUN_IS_A_CHANGE"
	theView      = "the knowledge view"
	kindRules    = "rules and facts"
	kindRows     = "a row per line with a cell per column"
	plainLang    = "plain language"
	stdoutPlace  = "standard output"
	stderrPlace  = "standard error"
	brokenAnswer = "broken"
	keepRules    = "every rule with its id"
	keepFacts    = "every fact with its id"
	keepReasons  = "every reason for every derived fact"
	keepCert     = "the certificate"
	keepNots     = "every not condition a derived fact rests on"
	partHashes   = "the hash of every file engine.go loads"
	partAnswer   = "the answer"
)

var computedAs = map[string]string{
	"a rule id":    "the first 16 hex digits of the sha256 of the rule lines joined by newlines",
	"a fact id":    "the first 16 hex digits of the sha256 of the fact as one plain line",
	"a row name":   "the file name and a colon and the line number",
	"a cell value": "the cell text read as a plain value",
}

var knownKeeps = map[string]bool{keepRules: true, keepFacts: true, keepReasons: true, keepCert: true, keepNots: true}

var knownParts = map[string]bool{partHashes: true, partAnswer: true}

type valKind int

const (
	vStr valKind = iota
	vNum
	vBlank
)

type pval struct {
	kind   valKind
	s      string
	n      int64
	quoted bool
}

const (
	fSentence = iota
	fIs
	fVerb
	fBuiltin
)

type patom struct {
	neg    bool
	form   int
	phrase string
	args   []pval
}

type builtinDef struct {
	phrase string
	min    int
	max    int
}

var builtinDefs = []builtinDef{
	{"ends with", 2, 2},
	{"starts with", 2, 2},
	{"differs from", 2, 2},
	{"is before", 2, 2},
	{"is the difference of", 3, 3},
	{"is the join of", 2, 64},
}

var (
	blankShape = regexp.MustCompile(`^\[[^\[\]]*\]$`)
	wordShape  = regexp.MustCompile(`^[a-z][a-z0-9]*$`)
	intShape   = regexp.MustCompile(`^(0|-?[1-9][0-9]*)$`)
)

func findBuiltin(phrase string) (builtinDef, bool) {
	for _, b := range builtinDefs {
		if b.phrase == phrase {
			return b, true
		}
	}
	return builtinDef{}, false
}

func validWords(s string) bool {
	if s == "" {
		return false
	}
	for _, w := range strings.Split(s, " ") {
		if !wordShape.MatchString(w) {
			return false
		}
	}
	return true
}

func plainValue(s string) pval {
	if intShape.MatchString(s) {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil {
			return pval{kind: vNum, n: n}
		}
	}
	return pval{kind: vStr, s: s}
}

func isControl(r rune) bool {
	return r < 0x20 || r == 0x7f
}

func readQuoted(text string, i int) (string, int, error) {
	if text[i] == '\'' {
		j := strings.IndexByte(text[i+1:], '\'')
		if j < 0 {
			return "", 0, fmt.Errorf("a quote is not closed")
		}
		return text[i+1 : i+1+j], i + 2 + j, nil
	}
	var b strings.Builder
	k := i + 1
	for k < len(text) {
		c := text[k]
		if c == '"' {
			return b.String(), k + 1, nil
		}
		if c != '\\' {
			b.WriteByte(c)
			k++
			continue
		}
		if k+1 >= len(text) {
			return "", 0, fmt.Errorf("a quote ends with a backslash")
		}
		switch text[k+1] {
		case '\\':
			b.WriteByte('\\')
		case '"':
			b.WriteByte('"')
		case 'n':
			b.WriteByte('\n')
		case 't':
			b.WriteByte('\t')
		case 'r':
			b.WriteByte('\r')
		case 'x':
			if k+3 >= len(text) {
				return "", 0, fmt.Errorf("a quote has a short hex escape")
			}
			v, err := strconv.ParseUint(text[k+2:k+4], 16, 8)
			if err != nil {
				return "", 0, fmt.Errorf("a quote has a bad hex escape")
			}
			b.WriteByte(byte(v))
			k += 4
			continue
		default:
			return "", 0, fmt.Errorf("a quote has an unknown escape")
		}
		k += 2
	}
	return "", 0, fmt.Errorf("a quote is not closed")
}

func bareValue(raw string) (pval, error) {
	if raw == "" {
		return pval{}, fmt.Errorf("a value is empty")
	}
	if blankShape.MatchString(raw) {
		name := raw[1 : len(raw)-1]
		if !validWords(name) {
			return pval{}, fmt.Errorf("the blank %s is not named with lowercase words", raw)
		}
		return pval{kind: vBlank, s: name}, nil
	}
	return plainValue(raw), nil
}

func splitParts(text string) ([]pval, error) {
	var out []pval
	i := 0
	for {
		if i < len(text) && (text[i] == '"' || text[i] == '\'') {
			v, next, err := readQuoted(text, i)
			if err != nil {
				return nil, err
			}
			out = append(out, pval{kind: vStr, s: v, quoted: true})
			i = next
		} else {
			j := strings.Index(text[i:], ", ")
			raw := text[i:]
			if j >= 0 {
				raw = text[i : i+j]
			}
			v, err := bareValue(raw)
			if err != nil {
				return nil, err
			}
			out = append(out, v)
			i += len(raw)
		}
		if i >= len(text) {
			return out, nil
		}
		if !strings.HasPrefix(text[i:], ", ") {
			return nil, fmt.Errorf("a quoted value is not followed by a comma")
		}
		i += 2
		if i >= len(text) {
			return nil, fmt.Errorf("the line ends with a comma")
		}
	}
}

func toAtom(parts []pval, cond bool) (patom, error) {
	if len(parts) == 1 {
		p := parts[0]
		if p.kind != vStr || p.quoted || !validWords(p.s) {
			return patom{}, fmt.Errorf("a line of one part must be lowercase words")
		}
		return patom{form: fSentence, phrase: p.s}, nil
	}
	if len(parts) == 2 {
		return patom{}, fmt.Errorf("a line needs one part or at least three parts")
	}
	verb := parts[1]
	if verb.kind != vStr || verb.quoted || !validWords(verb.s) {
		return patom{}, fmt.Errorf("the second part of a line must be lowercase words")
	}
	args := append([]pval{parts[0]}, parts[2:]...)
	if b, ok := findBuiltin(verb.s); ok {
		if !cond {
			return patom{}, fmt.Errorf("%s is built in and only works in a condition", verb.s)
		}
		if len(args) < b.min || len(args) > b.max {
			return patom{}, fmt.Errorf("%s takes a different number of values", verb.s)
		}
		return patom{form: fBuiltin, phrase: verb.s, args: args}, nil
	}
	if verb.s == "is" && len(parts) == 3 {
		o := parts[2]
		if o.kind == vStr && !o.quoted && validWords(o.s) {
			return patom{form: fIs, phrase: o.s, args: []pval{parts[0]}}, nil
		}
	}
	return patom{form: fVerb, phrase: verb.s, args: args}, nil
}

func symbolOf(phrase string) string {
	return strings.ReplaceAll(phrase, " ", "_")
}

func (a patom) symbol() string {
	return symbolOf(a.phrase)
}

func varName(blank string) string {
	var b strings.Builder
	for _, w := range strings.Split(blank, " ") {
		b.WriteString(strings.ToUpper(w[:1]))
		b.WriteString(w[1:])
	}
	return b.String()
}

func blankName(v string) string {
	var words []string
	cur := ""
	for _, r := range v {
		if unicode.IsUpper(r) {
			if cur != "" {
				words = append(words, cur)
			}
			cur = string(unicode.ToLower(r))
			continue
		}
		cur += string(r)
	}
	if cur != "" {
		words = append(words, cur)
	}
	return strings.Join(words, " ")
}

func mangleTerm(v pval) string {
	switch v.kind {
	case vBlank:
		return varName(v.s)
	case vNum:
		return strconv.FormatInt(v.n, 10)
	}
	return ast.String(v.s).String()
}

func (a patom) mangleText() (string, error) {
	args := make([]string, len(a.args))
	for i, v := range a.args {
		args[i] = mangleTerm(v)
	}
	if a.form == fBuiltin {
		if a.neg {
			return "", fmt.Errorf("the built in %s cannot be negated", a.phrase)
		}
		switch a.phrase {
		case "ends with":
			return ":string:ends_with(" + args[0] + ", " + args[1] + ")", nil
		case "starts with":
			return ":string:starts_with(" + args[0] + ", " + args[1] + ")", nil
		case "differs from":
			return args[0] + " != " + args[1], nil
		case "is before":
			return ":lt(" + args[0] + ", " + args[1] + ")", nil
		case "is the difference of":
			return args[0] + " = fn:minus(" + args[1] + ", " + args[2] + ")", nil
		case "is the join of":
			return args[0] + " = fn:string:concat(" + strings.Join(args[1:], ", ") + ")", nil
		}
		return "", fmt.Errorf("%s has no meaning in mangle", a.phrase)
	}
	s := a.symbol() + "(" + strings.Join(args, ", ") + ")"
	if a.neg {
		s = "!" + s
	}
	return s, nil
}

func translateLine(line string) (string, error) {
	neg := false
	rest := line
	if strings.HasPrefix(rest, "not ") {
		neg = true
		rest = rest[4:]
	}
	parts, err := splitParts(rest)
	if err != nil {
		return "", err
	}
	a, err := toAtom(parts, true)
	if err != nil {
		return "", err
	}
	a.neg = neg
	t, err := a.mangleText()
	if err != nil {
		return "", err
	}
	if a.form == fBuiltin || a.neg {
		return t, nil
	}
	return t + ".", nil
}

func fromBase(t ast.BaseTerm) (pval, error) {
	switch x := t.(type) {
	case ast.Variable:
		return pval{kind: vBlank, s: blankName(x.Symbol)}, nil
	case ast.Constant:
		switch x.Type {
		case ast.StringType:
			return pval{kind: vStr, s: x.Symbol}, nil
		case ast.NumberType:
			return pval{kind: vNum, n: x.NumValue}, nil
		}
	}
	return pval{}, fmt.Errorf("%v cannot be read back", t)
}

func fromBases(ts []ast.BaseTerm) ([]pval, error) {
	out := make([]pval, len(ts))
	for i, t := range ts {
		v, err := fromBase(t)
		if err != nil {
			return nil, err
		}
		out[i] = v
	}
	return out, nil
}

func fromMangleAtom(a ast.Atom) (patom, error) {
	args, err := fromBases(a.Args)
	if err != nil {
		return patom{}, err
	}
	sym := a.Predicate.Symbol
	switch sym {
	case ":string:ends_with":
		return patom{form: fBuiltin, phrase: "ends with", args: args}, nil
	case ":string:starts_with":
		return patom{form: fBuiltin, phrase: "starts with", args: args}, nil
	case ":lt":
		return patom{form: fBuiltin, phrase: "is before", args: args}, nil
	}
	phrase := strings.ReplaceAll(sym, "_", " ")
	if !validWords(phrase) {
		return patom{}, fmt.Errorf("%s cannot be read back", sym)
	}
	switch len(args) {
	case 0:
		return patom{form: fSentence, phrase: phrase}, nil
	case 1:
		return patom{form: fIs, phrase: phrase, args: args}, nil
	}
	return patom{form: fVerb, phrase: phrase, args: args}, nil
}

func fromMangleTerm(t ast.Term) (patom, error) {
	switch x := t.(type) {
	case ast.Atom:
		return fromMangleAtom(x)
	case ast.NegAtom:
		a, err := fromMangleAtom(x.Atom)
		a.neg = true
		return a, err
	case ast.Ineq:
		args, err := fromBases([]ast.BaseTerm{x.Left, x.Right})
		return patom{form: fBuiltin, phrase: "differs from", args: args}, err
	case ast.Eq:
		fn, ok := x.Right.(ast.ApplyFn)
		if !ok {
			return patom{}, fmt.Errorf("%v cannot be read back", t)
		}
		args, err := fromBases(append([]ast.BaseTerm{x.Left}, fn.Args...))
		if err != nil {
			return patom{}, err
		}
		switch fn.Function.Symbol {
		case "fn:minus":
			return patom{form: fBuiltin, phrase: "is the difference of", args: args}, nil
		case "fn:string:concat":
			return patom{form: fBuiltin, phrase: "is the join of", args: args}, nil
		}
	}
	return patom{}, fmt.Errorf("%v cannot be read back", t)
}

func bareSafe(s string) bool {
	if s == "" || strings.Contains(s, ", ") || strings.TrimSpace(s) != s {
		return false
	}
	if s[0] == '"' || s[0] == '\'' {
		return false
	}
	if blankShape.MatchString(s) || intShape.MatchString(s) {
		return false
	}
	return strings.IndexFunc(s, isControl) < 0
}

func quote(s string) string {
	ctrl := strings.IndexFunc(s, isControl) >= 0
	if !ctrl && !strings.ContainsAny(s, "\"\\") {
		return "\"" + s + "\""
	}
	if !ctrl && !strings.Contains(s, "'") {
		return "'" + s + "'"
	}
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
		case c == '\r':
			b.WriteString(`\r`)
		case c < 0x20 || c == 0x7f:
			fmt.Fprintf(&b, `\x%02x`, c)
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func renderValue(v pval, force bool, avoidNot bool) string {
	switch v.kind {
	case vBlank:
		return "[" + v.s + "]"
	case vNum:
		return strconv.FormatInt(v.n, 10)
	}
	if !force && bareSafe(v.s) && !(avoidNot && strings.HasPrefix(v.s, "not ")) {
		return v.s
	}
	return quote(v.s)
}

func (a patom) render(cond bool) string {
	var parts []string
	switch a.form {
	case fSentence:
		parts = []string{a.phrase}
	case fIs:
		parts = []string{renderValue(a.args[0], false, cond), "is", a.phrase}
	default:
		parts = []string{renderValue(a.args[0], false, cond), a.phrase}
		for _, v := range a.args[1:] {
			force := a.form == fVerb && a.phrase == "is" && len(a.args) == 2 && v.kind == vStr && validWords(v.s)
			parts = append(parts, renderValue(v, force, false))
		}
	}
	s := strings.Join(parts, ", ")
	if a.neg {
		s = "not " + s
	}
	return s
}

func renderAtom(a ast.Atom) string {
	p, err := fromMangleAtom(a)
	if err != nil {
		return a.String()
	}
	return p.render(false)
}

func constToPval(c ast.Constant) pval {
	if c.Type == ast.NumberType {
		return pval{kind: vNum, n: c.NumValue}
	}
	return pval{kind: vStr, s: c.Symbol}
}

func pvalConst(v pval) ast.Constant {
	if v.kind == vNum {
		return ast.Number(v.n)
	}
	return ast.String(v.s)
}

func str(t ast.BaseTerm) (string, bool) {
	c, ok := t.(ast.Constant)
	if !ok || c.Type != ast.StringType {
		return "", false
	}
	return c.Symbol, true
}

func shortHash(text string) string {
	sum := sha256.Sum256([]byte(text))
	return hex.EncodeToString(sum[:])[:16]
}

func fullHash(data []byte) string {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}

type stmt struct {
	file   string
	line   int
	name   string
	raw    []string
	head   patom
	conds  []patom
	clause ast.Clause
	fact   bool
	bad    bool
}

func (s *stmt) id() string {
	return shortHash(strings.Join(s.raw, "\n"))
}

func condLines(conds []patom) []string {
	var out []string
	for i, c := range conds {
		kw := "    and "
		if i == 0 {
			kw = "    if "
		}
		out = append(out, kw+c.render(true))
	}
	return out
}

func (s *stmt) canonical() []string {
	return append([]string{s.head.render(false)}, condLines(s.conds)...)
}

func (s *stmt) mangleText() (string, error) {
	h, err := s.head.mangleText()
	if err != nil {
		return "", err
	}
	if len(s.conds) == 0 {
		return h + ".", nil
	}
	var cs []string
	for _, c := range s.conds {
		t, err := c.mangleText()
		if err != nil {
			return "", err
		}
		cs = append(cs, t)
	}
	return h + " :- " + strings.Join(cs, ", ") + ".", nil
}

func (s *stmt) readsBack() bool {
	h, err := fromMangleAtom(s.clause.Head)
	if err != nil {
		return false
	}
	var conds []patom
	for _, p := range s.clause.Premises {
		c, err := fromMangleTerm(p)
		if err != nil {
			return false
		}
		conds = append(conds, c)
	}
	lines := append([]string{h.render(false)}, condLines(conds)...)
	if len(lines) != len(s.raw) {
		return false
	}
	for i := range lines {
		if lines[i] != s.raw[i] {
			return false
		}
	}
	return true
}

func (s *stmt) atoms() []patom {
	return append([]patom{s.head}, s.conds...)
}

func parsePlain(file, text string) ([]*stmt, []string) {
	var out []*stmt
	var problems []string
	lines := strings.Split(text, "\n")
	if len(lines) > 0 && lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	var cur *stmt
	fail := func(s *stmt, no int, err error) {
		problems = append(problems, fmt.Sprintf("%s:%d: %v", file, no, err))
		if s != nil {
			s.bad = true
		}
	}
	for i, ln := range lines {
		no := i + 1
		if strings.TrimSpace(ln) == "" {
			cur = nil
			continue
		}
		if ln[0] == ' ' || ln[0] == '\t' {
			if cur == nil {
				fail(nil, no, fmt.Errorf("a condition has no rule above it"))
				continue
			}
			cur.raw = append(cur.raw, ln)
			if cur.bad {
				continue
			}
			t := strings.TrimLeft(ln, " \t")
			var rest string
			switch {
			case strings.HasPrefix(t, "if "):
				rest = t[3:]
			case strings.HasPrefix(t, "and "):
				rest = t[4:]
			default:
				fail(cur, no, fmt.Errorf("a condition must start with if or and"))
				continue
			}
			neg := false
			if strings.HasPrefix(rest, "not ") {
				neg = true
				rest = rest[4:]
			}
			parts, err := splitParts(rest)
			if err != nil {
				fail(cur, no, err)
				continue
			}
			a, err := toAtom(parts, true)
			if err != nil {
				fail(cur, no, err)
				continue
			}
			a.neg = neg
			cur.conds = append(cur.conds, a)
			continue
		}
		cur = &stmt{file: file, line: no, name: fmt.Sprintf("%s:%d", file, no), raw: []string{ln}}
		out = append(out, cur)
		parts, err := splitParts(ln)
		if err != nil {
			fail(cur, no, err)
			continue
		}
		a, err := toAtom(parts, false)
		if err != nil {
			fail(cur, no, err)
			continue
		}
		cur.head = a
	}
	return out, problems
}

type pattern struct {
	text  string
	sym   string
	arity int
	slots []string
}

func parsePattern(text string) (pattern, error) {
	type seg struct {
		slot bool
		s    string
	}
	var segs []seg
	rest := text
	for rest != "" {
		if rest[0] == '[' {
			j := strings.IndexByte(rest, ']')
			if j < 0 {
				return pattern{}, fmt.Errorf("the fact pattern %q has an open slot", text)
			}
			name := rest[1:j]
			if !validWords(name) {
				return pattern{}, fmt.Errorf("the fact pattern %q has a slot that is not lowercase words", text)
			}
			segs = append(segs, seg{true, name})
			rest = rest[j+1:]
			continue
		}
		w := rest
		if j := strings.IndexByte(rest, '['); j >= 0 {
			w = rest[:j]
		}
		rest = rest[len(w):]
		if t := strings.TrimSpace(w); t != "" {
			segs = append(segs, seg{false, t})
		}
	}
	p := pattern{text: text}
	var parts []string
	for _, sg := range segs {
		if sg.slot {
			p.slots = append(p.slots, sg.s)
			parts = append(parts, "["+sg.s+"]")
		} else {
			parts = append(parts, sg.s)
		}
	}
	bad := fmt.Errorf("%q is not a fact pattern", text)
	if strings.Join(parts, " ") != text {
		return pattern{}, bad
	}
	switch {
	case len(segs) == 1 && !segs[0].slot:
		if !validWords(segs[0].s) {
			return pattern{}, bad
		}
		p.sym = symbolOf(segs[0].s)
	case len(segs) >= 2 && segs[0].slot && !segs[1].slot:
		for _, sg := range segs[2:] {
			if !sg.slot {
				return pattern{}, bad
			}
		}
		w := segs[1].s
		if len(segs) == 2 {
			if !strings.HasPrefix(w, "is ") || !validWords(w[3:]) {
				return pattern{}, bad
			}
			p.sym = symbolOf(w[3:])
			p.arity = 1
			break
		}
		if _, builtin := findBuiltin(w); builtin || !validWords(w) {
			return pattern{}, bad
		}
		p.sym = symbolOf(w)
		p.arity = len(segs) - 1
	default:
		return pattern{}, bad
	}
	return p, nil
}

func isPatternBlank(name string) bool {
	return name == "fact pattern" || name == "any fact pattern" || name == "other fact pattern"
}

func posKey(sym string, i int) string {
	return sym + "/" + strconv.Itoa(i)
}

type loadedFile struct {
	name string
	data []byte
}

type kb struct {
	loaded    []loadedFile
	stmts     []*stmt
	base      []ast.Atom
	baseKeys  map[string]bool
	origin    map[string]string
	order     map[string]int
	pending   []ast.Atom
	declared  map[string]map[string]int
	problems  []string
	seenProb  map[string]bool
	isChange  bool
	toolFacts map[string]bool
	postFacts map[string]bool
	patterns  []pattern
}

func newKB() *kb {
	return &kb{
		baseKeys:  map[string]bool{},
		origin:    map[string]string{},
		order:     map[string]int{},
		declared:  map[string]map[string]int{},
		seenProb:  map[string]bool{},
		toolFacts: map[string]bool{},
		postFacts: map[string]bool{},
	}
}

func (k *kb) problem(text string) {
	if k.seenProb[text] {
		return
	}
	k.seenProb[text] = true
	k.problems = append(k.problems, text)
}

func (k *kb) addBase(a ast.Atom, origin string) {
	key := a.String()
	if k.baseKeys[key] {
		return
	}
	k.baseKeys[key] = true
	k.base = append(k.base, a)
	k.origin[key] = origin
	k.order[key] = len(k.order)
}

func (k *kb) groundFacts(sym string, arity int) []ast.Atom {
	var out []ast.Atom
	for _, a := range k.base {
		if a.Predicate.Symbol == sym && a.Predicate.Arity == arity {
			out = append(out, a)
		}
	}
	return out
}

func groundAtom(a ast.Atom) bool {
	for _, t := range a.Args {
		if _, ok := t.(ast.Constant); !ok {
			return false
		}
	}
	return true
}

func (k *kb) load() {
	queue := []string{entryFile}
	queued := map[string]bool{entryFile: true}
	for len(queue) > 0 {
		name := queue[0]
		queue = queue[1:]
		if strings.ContainsAny(name, `/\`) {
			continue
		}
		data, err := os.ReadFile(name)
		if err != nil {
			if !errors.Is(err, os.ErrNotExist) {
				k.problem(fmt.Sprintf("%s cannot be read: %v", name, err))
			}
			continue
		}
		kind := kindRules
		if name != entryFile {
			kind = k.kindOf(name)
		}
		switch kind {
		case kindRules:
			k.loaded = append(k.loaded, loadedFile{name, data})
			k.loadPlain(name, data)
		case kindRows:
			k.loaded = append(k.loaded, loadedFile{name, data})
			k.loadRows(name, data)
		case "":
		default:
			k.problem(fmt.Sprintf("engine.go cannot load %s as %s", name, kind))
		}
		for _, a := range k.groundFacts("loads", 2) {
			who, _ := str(a.Args[0])
			what, ok := str(a.Args[1])
			if who == selfName && ok && !queued[what] {
				queued[what] = true
				queue = append(queue, what)
			}
		}
	}
}

func (k *kb) kindOf(name string) string {
	best, lang := "", ""
	for _, a := range k.groundFacts("means", 2) {
		e, ok1 := str(a.Args[0])
		l, ok2 := str(a.Args[1])
		if ok1 && ok2 && strings.HasSuffix(name, e) && len(e) > len(best) {
			best, lang = e, l
		}
	}
	if lang == "" {
		k.problem(fmt.Sprintf("engine.go loads %s but no ending of it means a language", name))
		return ""
	}
	for _, a := range k.groundFacts("is_loaded_as", 2) {
		l, _ := str(a.Args[0])
		kind, ok := str(a.Args[1])
		if l == lang && ok {
			return kind
		}
	}
	k.problem(fmt.Sprintf("engine.go loads %s but %s is not loaded as anything", name, lang))
	return ""
}

func (k *kb) loadPlain(name string, data []byte) {
	stmts, probs := parsePlain(name, string(data))
	for _, p := range probs {
		k.problem(p)
	}
	for _, s := range stmts {
		if s.bad {
			continue
		}
		text, err := s.mangleText()
		if err != nil {
			k.problem(fmt.Sprintf("%s: %v", s.name, err))
			continue
		}
		cl, err := parse.Clause(text)
		if err != nil {
			k.problem(fmt.Sprintf("%s: %s cannot be read as mangle", s.name, text))
			continue
		}
		s.clause = cl
		s.fact = len(s.conds) == 0 && groundAtom(cl.Head)
		k.stmts = append(k.stmts, s)
		if s.fact {
			k.addBase(cl.Head, s.name)
		}
	}
}

func rowName(file string, line int) string {
	return fmt.Sprintf("%s:%d", file, line)
}

func cellValue(text string) ast.Constant {
	return pvalConst(plainValue(text))
}

func (k *kb) loadRows(name string, data []byte) {
	r := csv.NewReader(bytes.NewReader(data))
	r.FieldsPerRecord = -1
	header, err := r.Read()
	if err != nil {
		if err != io.EOF {
			k.problem(fmt.Sprintf("%s cannot be read as rows: %v", name, err))
		}
		return
	}
	for {
		rec, err := r.Read()
		if err == io.EOF {
			return
		}
		if err != nil {
			k.problem(fmt.Sprintf("%s cannot be read as rows: %v", name, err))
			return
		}
		line, _ := r.FieldPos(0)
		row := rowName(name, line)
		if len(rec) != len(header) {
			k.problem(fmt.Sprintf("%s has %d cells but %s has %d columns", row, len(rec), name, len(header)))
		}
		k.pending = append(k.pending, ast.NewAtom("is_a_row_of", ast.String(row), ast.String(name)))
		for i, cell := range rec {
			if i < len(header) {
				k.pending = append(k.pending, ast.NewAtom("has_the_cell", ast.String(row), ast.String(header[i]), cellValue(cell)))
			}
		}
	}
}

func (k *kb) collectPatterns() {
	pos := map[string]bool{}
	for _, s := range k.stmts {
		for _, a := range s.atoms() {
			if a.form == fBuiltin {
				continue
			}
			for i, v := range a.args {
				if v.kind == vBlank && isPatternBlank(v.s) {
					pos[posKey(a.symbol(), i)] = true
				}
			}
		}
	}
	seen := map[string]bool{}
	for {
		grew := false
		for _, s := range k.stmts {
			for _, a := range s.atoms() {
				if a.form == fBuiltin {
					continue
				}
				for i, v := range a.args {
					if v.kind != vStr || !pos[posKey(a.symbol(), i)] || seen[v.s] {
						continue
					}
					seen[v.s] = true
					p, err := parsePattern(v.s)
					if err != nil {
						k.problem(fmt.Sprintf("%s: %v", s.name, err))
						continue
					}
					k.patterns = append(k.patterns, p)
					for j, sl := range p.slots {
						if isPatternBlank(sl) && !pos[posKey(p.sym, j)] {
							pos[posKey(p.sym, j)] = true
							grew = true
						}
					}
				}
			}
		}
		if !grew {
			return
		}
	}
}

func (k *kb) declare() {
	for _, a := range k.groundFacts("creates_fact", 2) {
		who, ok1 := str(a.Args[0])
		what, ok2 := str(a.Args[1])
		if !ok1 || !ok2 {
			continue
		}
		p, err := parsePattern(what)
		if err != nil {
			k.problem(fmt.Sprintf("%s creates fact %v", who, err))
			continue
		}
		if k.declared[who] == nil {
			k.declared[who] = map[string]int{}
		}
		k.declared[who][p.sym] = p.arity
	}
}

func (k *kb) allowed(who string, a ast.Atom) bool {
	ar, ok := k.declared[who][a.Predicate.Symbol]
	if !ok || ar != a.Predicate.Arity {
		k.problem(fmt.Sprintf("%s makes %s facts but the spec does not say it creates them", who, a.Predicate.Symbol))
		return false
	}
	return true
}

func (k *kb) metaFacts() {
	add := func(sym string, args ...ast.BaseTerm) {
		k.pending = append(k.pending, ast.NewAtom(sym, args...))
	}
	for _, s := range k.stmts {
		name := ast.String(s.name)
		sym := s.head.symbol()
		add("has_the_id", name, pvalConst(plainValue(s.id())))
		add("has_a_rule_for", ast.String(s.file), ast.String(sym))
		add("defines", name, ast.String(sym))
		for _, c := range s.conds {
			if c.form != fBuiltin {
				add("refers_to", name, ast.String(c.symbol()))
			}
		}
		if sym == "breaks" && s.head.form == fVerb && len(s.head.args) == 2 && s.head.args[1].kind == vStr {
			add("lays_down", name, ast.String(s.head.args[1].s))
		}
		blanks := map[string]bool{}
		for _, a := range s.atoms() {
			for _, v := range a.args {
				if v.kind == vBlank && !blanks[v.s] {
					blanks[v.s] = true
					add("has_the_blank", name, ast.String(v.s))
				}
			}
		}
		if !s.readsBack() {
			add("read_back_differently", name)
		}
	}
	for _, p := range k.patterns {
		add("names", ast.String(p.text), ast.String(p.sym))
		for _, sl := range p.slots {
			add("has_the_slot", ast.String(p.text), ast.String(sl))
		}
	}
	if k.isChange {
		add("this_run_is_a_change")
	}
	for _, a := range k.pending {
		if k.allowed(selfName, a) {
			k.addBase(a, selfName)
		}
	}
	k.pending = nil
}

func (k *kb) checkArities() {
	seen := map[string]int{}
	note := func(sym string, n int) {
		if old, ok := seen[sym]; ok && old != n {
			k.problem(fmt.Sprintf("%s is used with %d values and with %d values", sym, old, n))
			return
		}
		seen[sym] = n
	}
	for _, s := range k.stmts {
		for _, a := range s.atoms() {
			if a.form != fBuiltin {
				note(a.symbol(), len(a.args))
			}
		}
	}
	for _, a := range k.base {
		note(a.Predicate.Symbol, a.Predicate.Arity)
	}
	var whos []string
	for who := range k.declared {
		whos = append(whos, who)
	}
	sort.Strings(whos)
	for _, who := range whos {
		var syms []string
		for sym := range k.declared[who] {
			syms = append(syms, sym)
		}
		sort.Strings(syms)
		for _, sym := range syms {
			note(sym, k.declared[who][sym])
		}
	}
}

type model struct {
	atoms []ast.Atom
	keys  map[string]bool
	bySym map[string][]ast.Atom
	first map[string]map[string][]ast.Atom
}

func newModel() *model {
	return &model{keys: map[string]bool{}, bySym: map[string][]ast.Atom{}, first: map[string]map[string][]ast.Atom{}}
}

func (m *model) add(a ast.Atom) bool {
	key := a.String()
	if m.keys[key] {
		return false
	}
	m.keys[key] = true
	m.atoms = append(m.atoms, a)
	s := a.Predicate.Symbol
	m.bySym[s] = append(m.bySym[s], a)
	if len(a.Args) > 0 {
		if m.first[s] == nil {
			m.first[s] = map[string][]ast.Atom{}
		}
		fk := a.Args[0].String()
		m.first[s][fk] = append(m.first[s][fk], a)
	}
	return true
}

func (m *model) facts(sym string, arity int) []ast.Atom {
	var out []ast.Atom
	for _, a := range m.bySym[sym] {
		if a.Predicate.Arity == arity {
			out = append(out, a)
		}
	}
	return out
}

func (k *kb) ruleSyms() map[string]bool {
	out := map[string]bool{}
	for _, s := range k.stmts {
		if !s.fact {
			out[s.clause.Head.Predicate.Symbol] = true
		}
	}
	return out
}

func (k *kb) evaluate(extra []ast.Atom) (*model, error) {
	rules := k.ruleSyms()
	var clauses []ast.Clause
	for _, s := range k.stmts {
		if !s.fact {
			clauses = append(clauses, s.clause)
		}
	}
	store := factstore.NewSimpleInMemoryStore()
	decls := map[ast.PredicateSym]ast.Decl{}
	declare := func(p ast.PredicateSym) {
		if !rules[p.Symbol] {
			decls[p] = ast.NewSyntheticDeclFromSym(p)
		}
	}
	for _, a := range k.base {
		store.Add(a)
		declare(a.Predicate)
	}
	for _, a := range extra {
		store.Add(a)
		declare(a.Predicate)
	}
	for _, syms := range k.declared {
		for sym, n := range syms {
			declare(ast.PredicateSym{Symbol: sym, Arity: n})
		}
	}
	info, err := analysis.AnalyzeOneUnit(parse.SourceUnit{Clauses: clauses}, decls)
	if err != nil {
		return nil, err
	}
	if err := engine.EvalProgram(info, store); err != nil {
		return nil, err
	}
	m := newModel()
	preds := store.ListPredicates()
	sort.Slice(preds, func(i, j int) bool { return preds[i].String() < preds[j].String() })
	for _, p := range preds {
		store.GetFacts(ast.NewQuery(p), func(a ast.Atom) error {
			m.add(a)
			return nil
		})
	}
	return m, nil
}

func (k *kb) fixpoint() (*model, error) {
	done := map[string]bool{}
	var returned []ast.Atom
	for round := 0; ; round++ {
		m, err := k.evaluate(returned)
		if err != nil {
			return nil, err
		}
		var pending []ast.Atom
		for _, c := range m.facts("calls", 3) {
			if !done[c.String()] {
				pending = append(pending, c)
			}
		}
		if len(pending) == 0 || round >= 32 {
			return m, nil
		}
		results := runCalls(k, m, pending)
		for _, c := range pending {
			done[c.String()] = true
			for _, a := range results[c.String()] {
				if k.allowed(toolsName, a) {
					returned = append(returned, a)
					k.toolFacts[a.String()] = true
				}
			}
		}
	}
}

type binding map[string]ast.Constant

func copyBinding(b binding) binding {
	out := make(binding, len(b)+2)
	for x, v := range b {
		out[x] = v
	}
	return out
}

func valueOf(v pval, b binding) (ast.Constant, bool) {
	if v.kind == vBlank {
		c, ok := b[v.s]
		return c, ok
	}
	return pvalConst(v), true
}

func ready(c patom, b binding) bool {
	if c.form != fBuiltin && !c.neg {
		return true
	}
	from := 0
	if c.form == fBuiltin && (c.phrase == "is the join of" || c.phrase == "is the difference of") {
		from = 1
	}
	for _, v := range c.args[from:] {
		if _, ok := valueOf(v, b); !ok {
			return false
		}
	}
	return true
}

func groundOf(a patom, b binding) (patom, bool) {
	g := patom{neg: a.neg, form: a.form, phrase: a.phrase}
	for _, v := range a.args {
		c, ok := valueOf(v, b)
		if !ok {
			return patom{}, false
		}
		g.args = append(g.args, constToPval(c))
	}
	return g, true
}

func atomOf(a patom, b binding) (ast.Atom, bool) {
	var args []ast.BaseTerm
	for _, v := range a.args {
		c, ok := valueOf(v, b)
		if !ok {
			return ast.Atom{}, false
		}
		args = append(args, c)
	}
	return ast.NewAtom(a.symbol(), args...), true
}

func unify(a patom, fact ast.Atom, b binding) (binding, bool) {
	nb := b
	copied := false
	for i, v := range a.args {
		c, ok := fact.Args[i].(ast.Constant)
		if !ok {
			return nil, false
		}
		if v.kind == vBlank {
			if old, ok := nb[v.s]; ok {
				if !old.Equals(c) {
					return nil, false
				}
				continue
			}
			if !copied {
				nb = copyBinding(b)
				copied = true
			}
			nb[v.s] = c
			continue
		}
		if !pvalConst(v).Equals(c) {
			return nil, false
		}
	}
	return nb, true
}

func assign(v pval, c ast.Constant, b binding) []binding {
	if old, ok := valueOf(v, b); ok {
		if old.Equals(c) {
			return []binding{b}
		}
		return nil
	}
	nb := copyBinding(b)
	nb[v.s] = c
	return []binding{nb}
}

func asText(c ast.Constant) (string, bool) {
	switch c.Type {
	case ast.StringType:
		return c.Symbol, true
	case ast.NumberType:
		return strconv.FormatInt(c.NumValue, 10), true
	}
	return "", false
}

func evalBuiltin(c patom, b binding) []binding {
	vals := make([]ast.Constant, len(c.args))
	for i, v := range c.args {
		vals[i], _ = valueOf(v, b)
	}
	yes := []binding{b}
	switch c.phrase {
	case "ends with", "starts with":
		if vals[0].Type != ast.StringType || vals[1].Type != ast.StringType {
			return nil
		}
		if c.phrase == "ends with" && strings.HasSuffix(vals[0].Symbol, vals[1].Symbol) {
			return yes
		}
		if c.phrase == "starts with" && strings.HasPrefix(vals[0].Symbol, vals[1].Symbol) {
			return yes
		}
	case "differs from":
		if !vals[0].Equals(vals[1]) {
			return yes
		}
	case "is before":
		if vals[0].Type == ast.NumberType && vals[1].Type == ast.NumberType && vals[0].NumValue < vals[1].NumValue {
			return yes
		}
	case "is the difference of":
		if vals[1].Type == ast.NumberType && vals[2].Type == ast.NumberType {
			return assign(c.args[0], ast.Number(vals[1].NumValue-vals[2].NumValue), b)
		}
	case "is the join of":
		var sb strings.Builder
		for _, v := range vals[1:] {
			t, ok := asText(v)
			if !ok {
				return nil
			}
			sb.WriteString(t)
		}
		return assign(c.args[0], ast.String(sb.String()), b)
	}
	return nil
}

func step(m *model, c patom, b binding) []binding {
	if c.form == fBuiltin {
		return evalBuiltin(c, b)
	}
	if c.neg {
		a, ok := atomOf(c, b)
		if !ok || m.keys[a.String()] {
			return nil
		}
		return []binding{b}
	}
	sym := c.symbol()
	candidates := m.bySym[sym]
	if len(c.args) > 0 {
		if v, ok := valueOf(c.args[0], b); ok {
			candidates = m.first[sym][v.String()]
		}
	}
	var out []binding
	for _, f := range candidates {
		if f.Predicate.Arity != len(c.args) {
			continue
		}
		if nb, ok := unify(c, f, b); ok {
			out = append(out, nb)
		}
	}
	return out
}

func solve(m *model, s *stmt, emit func(binding)) {
	done := make([]bool, len(s.conds))
	var rec func(b binding, left int)
	rec = func(b binding, left int) {
		if left == 0 {
			emit(b)
			return
		}
		idx := -1
		for i, c := range s.conds {
			if !done[i] && ready(c, b) {
				idx = i
				break
			}
		}
		if idx < 0 {
			return
		}
		done[idx] = true
		for _, nb := range step(m, s.conds[idx], b) {
			rec(nb, left-1)
		}
		done[idx] = false
	}
	rec(binding{}, len(s.conds))
}

type cond struct {
	text string
	neg  bool
}

type derivation struct {
	rule  string
	conds []cond
}

type derived struct {
	atom   ast.Atom
	derivs []derivation
}

func (k *kb) derive(m *model) map[string]*derived {
	out := map[string]*derived{}
	seen := map[string]bool{}
	for _, s := range k.stmts {
		if s.fact {
			continue
		}
		solve(m, s, func(b binding) {
			head, ok := atomOf(s.head, b)
			if !ok {
				return
			}
			d := derivation{rule: s.name}
			sig := s.name
			for _, c := range s.conds {
				g, ok := groundOf(c, b)
				if !ok {
					return
				}
				t := g.render(true)
				d.conds = append(d.conds, cond{text: t, neg: c.neg})
				sig += "\n" + t
			}
			key := head.String()
			if seen[key+"\n"+sig] {
				return
			}
			seen[key+"\n"+sig] = true
			if out[key] == nil {
				out[key] = &derived{atom: head}
			}
			out[key].derivs = append(out[key].derivs, d)
		})
	}
	keys := make([]string, 0, len(out))
	for key := range out {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	for _, key := range keys {
		if !m.keys[key] {
			k.problem(fmt.Sprintf("%s follows from the rules but mangle did not find it", renderAtom(out[key].atom)))
		}
	}
	rules := k.ruleSyms()
	for _, a := range m.atoms {
		key := a.String()
		if rules[a.Predicate.Symbol] && !k.baseKeys[key] && !k.toolFacts[key] && out[key] == nil {
			k.problem(fmt.Sprintf("mangle found %s but no rule gives a reason for it", renderAtom(a)))
		}
	}
	return out
}

func (k *kb) reasonFacts(m *model, ds map[string]*derived) {
	syms := map[string]int{}
	for _, a := range m.facts("gives_reasons_for", 2) {
		t, ok := str(a.Args[1])
		if !ok {
			continue
		}
		p, err := parsePattern(t)
		if err != nil {
			k.problem(err.Error())
			continue
		}
		syms[p.sym] = p.arity
	}
	var add []ast.Atom
	for _, a := range m.atoms {
		if n, ok := syms[a.Predicate.Symbol]; !ok || n != a.Predicate.Arity {
			continue
		}
		d := ds[a.String()]
		if d == nil {
			continue
		}
		line := renderAtom(a)
		for _, dv := range d.derivs {
			for _, c := range dv.conds {
				add = append(add, ast.NewAtom("holds_because", ast.String(line), ast.String(c.text)))
			}
		}
	}
	for _, h := range add {
		if k.allowed(selfName, h) && m.add(h) {
			k.postFacts[h.String()] = true
		}
	}
}

func (k *kb) checkInstructions(m *model) {
	for _, a := range m.facts("means_in_mangle", 2) {
		line, ok1 := str(a.Args[0])
		want, ok2 := str(a.Args[1])
		if !ok1 || !ok2 {
			k.problem(fmt.Sprintf("%s does not pair two texts", renderAtom(a)))
			continue
		}
		got, err := translateLine(line)
		if err != nil {
			k.problem(fmt.Sprintf("%s has no meaning in mangle: %v", line, err))
			continue
		}
		if got != want {
			k.problem(fmt.Sprintf("%s means %s in mangle, not %s", line, got, want))
		}
	}
	for _, a := range m.facts("is_computed_as", 2) {
		kind, _ := str(a.Args[0])
		method, _ := str(a.Args[1])
		if want, ok := computedAs[kind]; !ok || want != method {
			k.problem(fmt.Sprintf("engine.go cannot compute %s as %s", kind, method))
		}
	}
	for _, a := range m.facts("is_loaded_as", 2) {
		kind, _ := str(a.Args[1])
		if kind != kindRules && kind != kindRows {
			k.problem(fmt.Sprintf("engine.go cannot load anything as %s", kind))
		}
	}
	for _, a := range m.facts("prints_in", 2) {
		who, _ := str(a.Args[0])
		lang, _ := str(a.Args[1])
		if who == selfName && lang != plainLang {
			k.problem(fmt.Sprintf("engine.go cannot print in %s", lang))
		}
	}
	for _, a := range m.facts("prints_to", 2) {
		who, _ := str(a.Args[0])
		place, _ := str(a.Args[1])
		if who == selfName && place != stdoutPlace {
			k.problem(fmt.Sprintf("engine.go cannot print to %s", place))
		}
	}
	for _, a := range m.facts("keeps", 2) {
		kind, _ := str(a.Args[1])
		if !knownKeeps[kind] {
			k.problem(fmt.Sprintf("engine.go cannot keep %s", kind))
		}
	}
	for _, a := range m.facts("holds", 2) {
		part, _ := str(a.Args[1])
		if !knownParts[part] {
			k.problem(fmt.Sprintf("engine.go cannot put %s in a certificate", part))
		}
	}
}

func (k *kb) answer(m *model) string {
	set := map[string]bool{}
	for _, a := range m.facts("conforms", 2) {
		if s, ok := str(a.Args[1]); ok {
			set[s] = true
		}
	}
	if len(set) != 1 {
		k.problem("the folder does not conform with exactly one answer")
		return brokenAnswer
	}
	for s := range set {
		return s
	}
	return brokenAnswer
}

func (k *kb) exitCode(m *model, answer string) (int, bool) {
	var facts []ast.Atom
	if m != nil {
		facts = m.facts("exits_with", 2)
	} else {
		facts = k.groundFacts("exits_with", 2)
	}
	for _, a := range facts {
		if s, ok := str(a.Args[0]); ok && s == answer {
			if c, ok := a.Args[1].(ast.Constant); ok && c.Type == ast.NumberType {
				return int(c.NumValue), true
			}
		}
	}
	return 2, false
}

func (k *kb) problemLines() []string {
	var out []string
	for _, p := range k.problems {
		out = append(out, renderAtom(ast.NewAtom("a_problem", ast.String(p))))
	}
	return out
}

func (k *kb) addProblemFacts(m *model) {
	for _, p := range k.problems {
		a := ast.NewAtom("a_problem", ast.String(p))
		if k.declared[selfName]["a_problem"] == 1 && m.add(a) {
			k.postFacts[a.String()] = true
		}
	}
}

func (k *kb) viewLines(m *model, view string) []string {
	var lines []string
	if view == theView {
		last := ""
		for _, s := range k.stmts {
			if !m.keys[ast.NewAtom("in_the_knowledge_view", ast.String(s.name)).String()] {
				continue
			}
			if last != "" && s.file != last {
				lines = append(lines, "")
			}
			last = s.file
			lines = append(lines, s.canonical()...)
		}
		if last != "" {
			lines = append(lines, "")
		}
	}
	type group struct {
		p   pattern
		ord int
	}
	groups := map[string]*group{}
	for _, a := range m.facts("shows", 2) {
		v, _ := str(a.Args[0])
		t, ok := str(a.Args[1])
		if v != view || !ok {
			continue
		}
		p, err := parsePattern(t)
		if err != nil {
			continue
		}
		ord, ok := k.order[a.String()]
		if !ok {
			ord = 1 << 30
		}
		key := posKey(p.sym, p.arity)
		if g, ok := groups[key]; !ok || ord < g.ord || (ord == g.ord && p.text < g.p.text) {
			groups[key] = &group{p, ord}
		}
	}
	var list []*group
	for _, g := range groups {
		list = append(list, g)
	}
	sort.Slice(list, func(i, j int) bool {
		if list[i].ord != list[j].ord {
			return list[i].ord < list[j].ord
		}
		return list[i].p.text < list[j].p.text
	})
	for _, g := range list {
		var texts []string
		for _, a := range m.facts(g.p.sym, g.p.arity) {
			texts = append(texts, renderAtom(a))
		}
		if len(texts) == 0 {
			continue
		}
		sort.Strings(texts)
		lines = append(lines, texts...)
		lines = append(lines, "")
	}
	return lines
}

func (k *kb) originOf(a ast.Atom) string {
	key := a.String()
	if o, ok := k.origin[key]; ok {
		return o
	}
	if k.toolFacts[key] {
		return toolsName
	}
	if k.postFacts[key] {
		return selfName
	}
	return "derived"
}

type target struct {
	view  string
	path  string
	kinds map[string]bool
	parts map[string]bool
}

func (k *kb) targets(m *model, answer string) []target {
	var out []target
	for _, a := range m.facts("is_published_to", 2) {
		view, _ := str(a.Args[0])
		store, _ := str(a.Args[1])
		limited, allowed := false, false
		for _, w := range m.facts("is_published_only_when", 2) {
			if s, _ := str(w.Args[0]); s == view {
				limited = true
				if s, _ := str(w.Args[1]); s == answer {
					allowed = true
				}
			}
		}
		if limited && !allowed {
			continue
		}
		t := target{view: view, kinds: map[string]bool{}, parts: map[string]bool{}}
		for _, f := range m.facts("is_the_sqlite_file", 2) {
			if s, _ := str(f.Args[0]); s == store {
				t.path, _ = str(f.Args[1])
			}
		}
		if t.path == "" {
			k.problem(fmt.Sprintf("%s is published to %s but %s is no sqlite file", view, store, store))
			continue
		}
		for _, f := range m.facts("keeps", 2) {
			if s, _ := str(f.Args[0]); s == store {
				kind, _ := str(f.Args[1])
				t.kinds[kind] = true
			}
		}
		for _, f := range m.facts("holds", 2) {
			part, _ := str(f.Args[1])
			t.parts[part] = true
		}
		out = append(out, t)
	}
	return out
}

func (k *kb) writeStore(t target, m *model, lines []string, ds map[string]*derived, answer string) error {
	tmp := t.path + ".new"
	os.Remove(tmp)
	db, err := sql.Open("sqlite", tmp)
	if err != nil {
		return err
	}
	tx, err := db.Begin()
	if err != nil {
		db.Close()
		return err
	}
	exec := func(q string, args ...any) {
		if err == nil {
			_, err = tx.Exec(q, args...)
		}
	}
	exec(`create table view (position integer primary key, line text not null)`)
	for i, l := range lines {
		exec(`insert into view values (?, ?)`, i+1, l)
	}
	if t.kinds[keepRules] {
		exec(`create table rule (name text primary key, id text not null, file text not null, line integer not null, text text not null)`)
		for _, s := range k.stmts {
			exec(`insert into rule values (?, ?, ?, ?, ?)`, s.name, s.id(), s.file, s.line, strings.Join(s.raw, "\n"))
		}
	}
	if t.kinds[keepFacts] {
		exec(`create table fact (id text primary key, text text not null, origin text not null)`)
		for _, a := range m.atoms {
			line := renderAtom(a)
			exec(`insert or ignore into fact values (?, ?, ?)`, shortHash(line), line, k.originOf(a))
		}
	}
	keys := make([]string, 0, len(ds))
	for key := range ds {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	if t.kinds[keepReasons] {
		exec(`create table reason (fact text not null, derivation integer not null, position integer not null, rule text not null, condition text not null, negated integer not null)`)
		for _, key := range keys {
			fid := shortHash(renderAtom(ds[key].atom))
			for di, d := range ds[key].derivs {
				for ci, c := range d.conds {
					neg := 0
					if c.neg {
						neg = 1
					}
					exec(`insert into reason values (?, ?, ?, ?, ?, ?)`, fid, di+1, ci+1, d.rule, c.text, neg)
				}
			}
		}
	}
	if t.kinds[keepNots] {
		exec(`create table not_condition (fact text not null, derivation integer not null, rule text not null, condition text not null)`)
		for _, key := range keys {
			fid := shortHash(renderAtom(ds[key].atom))
			for di, d := range ds[key].derivs {
				for _, c := range d.conds {
					if c.neg {
						exec(`insert into not_condition values (?, ?, ?, ?)`, fid, di+1, d.rule, c.text)
					}
				}
			}
		}
	}
	if t.kinds[keepCert] {
		exec(`create table certificate (part text not null, name text not null, value text not null)`)
		if t.parts[partHashes] {
			for _, f := range k.loaded {
				exec(`insert into certificate values (?, ?, ?)`, partHashes, f.name, fullHash(f.data))
			}
		}
		if t.parts[partAnswer] {
			exec(`insert into certificate values (?, ?, ?)`, partAnswer, "the folder", answer)
		}
	}
	if err != nil {
		tx.Rollback()
		db.Close()
		os.Remove(tmp)
		return err
	}
	if err := tx.Commit(); err != nil {
		db.Close()
		os.Remove(tmp)
		return err
	}
	if err := db.Close(); err != nil {
		os.Remove(tmp)
		return err
	}
	return os.Rename(tmp, t.path)
}

func writeLines(lines []string) {
	w := bufio.NewWriter(os.Stdout)
	for _, l := range lines {
		w.WriteString(l)
		w.WriteByte('\n')
	}
	w.Flush()
}

func (k *kb) broken() int {
	writeLines(k.problemLines())
	code, _ := k.exitCode(nil, brokenAnswer)
	return code
}

func run() int {
	k := newKB()
	k.isChange = os.Getenv(changeEnv) != ""
	k.load()
	k.collectPatterns()
	k.declare()
	k.metaFacts()
	k.checkArities()
	if len(k.problems) > 0 {
		return k.broken()
	}
	m, err := k.fixpoint()
	if err != nil {
		k.problem(fmt.Sprintf("mangle cannot evaluate the rules: %v", err))
		return k.broken()
	}
	ds := k.derive(m)
	k.reasonFacts(m, ds)
	k.checkInstructions(m)
	answer := k.answer(m)
	if _, ok := k.exitCode(m, answer); !ok {
		k.problem(fmt.Sprintf("%s exits with no code", answer))
	}
	if len(k.problems) > 0 {
		answer = brokenAnswer
	}
	k.addProblemFacts(m)
	for _, t := range k.targets(m, answer) {
		if err := k.writeStore(t, m, k.viewLines(m, t.view), ds, answer); err != nil {
			k.problem(fmt.Sprintf("%s cannot be written: %v", t.path, err))
		}
	}
	if len(k.problems) > 0 && answer != brokenAnswer {
		answer = brokenAnswer
		k.addProblemFacts(m)
	}
	var lines []string
	for _, v := range k.printedViews(m) {
		lines = append(lines, k.viewLines(m, v)...)
	}
	writeLines(lines)
	code, _ := k.exitCode(m, answer)
	return code
}

func (k *kb) printedViews(m *model) []string {
	type view struct {
		name string
		ord  int
	}
	var views []view
	for _, a := range m.facts("prints", 2) {
		who, _ := str(a.Args[0])
		v, ok := str(a.Args[1])
		if who != selfName || !ok {
			continue
		}
		ord, known := k.order[a.String()]
		if !known {
			ord = 1 << 30
		}
		views = append(views, view{v, ord})
	}
	sort.Slice(views, func(i, j int) bool {
		if views[i].ord != views[j].ord {
			return views[i].ord < views[j].ord
		}
		return views[i].name < views[j].name
	})
	var out []string
	for _, v := range views {
		out = append(out, v.name)
	}
	return out
}

func main() {
	os.Exit(run())
}
