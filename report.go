package main

import (
	"fmt"
	"html/template"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/factstore"
)

type note struct {
	Word    string
	Pattern string
	Finding bool
	Values  []string
}

type shownRule struct {
	Text  template.HTML
	Notes []note
}

type shownChange struct {
	Name  string
	Notes []note
}

type shownConcept struct {
	ID      string
	Name    string
	Flagged bool
	Notes   []note
	Rules   []shownRule
	Changes []shownChange
}

type shownWord struct {
	ID    string
	Name  string
	Notes []note
	Rules []shownRule
}

type shownOutput struct {
	Word  string
	Facts []string
	Open  bool
}

type page struct {
	Title    string
	Answer   string
	Code     int
	Good     bool
	Problems []string
	Language string
	Rounds   int
	Concepts []shownConcept
	Words    []shownWord
	Outputs  []shownOutput
	Rules    int
}

type reader struct {
	store  factstore.FactStore
	about  map[string][]ast.Atom
	wordID map[string]string
	opens  map[string]map[string]bool
	headOf map[string]string
}

var structure = map[string]bool{"shows": true, "shows_change": true, "opens_into": true, "explained_by": true}

func writeReport(o outcome) (string, error) {
	if o.store == nil {
		return "", nil
	}
	r := &reader{store: o.store, about: map[string][]ast.Atom{}, wordID: map[string]string{}, opens: map[string]map[string]bool{}, headOf: map[string]string{}}
	targets := r.texts("output_file", 1, 0)
	if len(targets) == 0 {
		return "", nil
	}
	languages := r.texts("printed_in", 1, 0)
	if len(languages) == 0 {
		return "", fmt.Errorf("the program does not say what language to print in")
	}
	for _, l := range languages {
		if l != "mangle" {
			return "", fmt.Errorf("cannot print in %s", l)
		}
	}
	p := page{
		Title:    folderName(o.dir),
		Answer:   o.answer,
		Code:     o.code,
		Good:     o.code == 0,
		Problems: o.problems,
		Language: strings.Join(languages, ", "),
		Rounds:   o.rounds,
	}
	outputs := r.texts("output", 1, 0)
	for _, w := range outputs {
		facts := r.factsOf(w)
		var printed []string
		for _, f := range facts {
			printed = append(printed, f.String()+".")
			if structure[w] {
				continue
			}
			seen := map[string]bool{}
			for _, arg := range f.Args {
				k := key(arg)
				if !seen[k] {
					seen[k] = true
					r.about[k] = append(r.about[k], f)
				}
			}
		}
		sort.Strings(printed)
		p.Outputs = append(p.Outputs, shownOutput{Word: w, Facts: printed, Open: len(printed) > 0 && len(printed) <= 12})
	}
	for _, f := range r.pairs("opens_into") {
		if r.opens[f[0]] == nil {
			r.opens[f[0]] = map[string]bool{}
		}
		r.opens[f[0]][f[1]] = true
	}
	explained := map[string][]string{}
	for _, f := range r.pairs("explained_by") {
		explained[f[0]] = append(explained[f[0]], f[1])
		r.headOf[f[1]] = f[0]
		if r.opens[f[1]] == nil {
			r.opens[f[1]] = map[string]bool{}
		}
		r.opens[f[1]][f[0]] = true
	}
	words := keys(explained)
	for i, w := range words {
		r.wordID[w] = fmt.Sprintf("w%d", i+1)
	}
	allRules := map[string]bool{}
	for _, w := range words {
		sw := shownWord{ID: r.wordID[w], Name: w, Notes: r.notes(w, nil)}
		for _, rule := range sorted(explained[w]) {
			sw.Rules = append(sw.Rules, r.rule(rule))
			allRules[rule] = true
		}
		p.Words = append(p.Words, sw)
	}
	shows := map[string][]string{}
	for _, f := range r.pairs("shows") {
		shows[f[0]] = append(shows[f[0]], f[1])
	}
	changes := map[string][]string{}
	for _, f := range r.pairs("shows_change") {
		changes[f[0]] = append(changes[f[0]], f[1])
	}
	names := map[string]bool{}
	for k := range shows {
		names[k] = true
	}
	for k := range changes {
		names[k] = true
	}
	for i, c := range keys(names) {
		heads := map[string]bool{}
		for _, rule := range shows[c] {
			heads[r.headOf[rule]] = true
		}
		sc := shownConcept{ID: fmt.Sprintf("c%d", i+1), Name: c, Notes: r.notes(c, heads)}
		for _, n := range sc.Notes {
			sc.Flagged = sc.Flagged || n.Finding
		}
		for _, rule := range sorted(shows[c]) {
			sc.Rules = append(sc.Rules, r.rule(rule))
			allRules[rule] = true
		}
		for _, ch := range sorted(changes[c]) {
			sc.Changes = append(sc.Changes, shownChange{Name: ch, Notes: r.notes(ch, nil)})
		}
		p.Concepts = append(p.Concepts, sc)
	}
	sort.SliceStable(p.Concepts, func(i, j int) bool {
		return p.Concepts[i].Flagged && !p.Concepts[j].Flagged
	})
	p.Rules = len(allRules)
	var b strings.Builder
	if err := pageTemplate.Execute(&b, p); err != nil {
		return "", err
	}
	var written []string
	for _, t := range targets {
		if !filepath.IsLocal(t) {
			return "", fmt.Errorf("%s is outside the folder", t)
		}
		full := filepath.Join(o.dir, filepath.FromSlash(t))
		if err := os.WriteFile(full, []byte(b.String()), 0o644); err != nil {
			return "", err
		}
		written = append(written, t)
	}
	return strings.Join(written, ", "), nil
}

func folderName(dir string) string {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return dir
	}
	return filepath.Base(abs)
}

func key(t ast.BaseTerm) string {
	if c, ok := t.(ast.Constant); ok {
		if s, err := c.StringValue(); err == nil {
			return s
		}
	}
	return t.String()
}

func (r *reader) factsOf(word string) []ast.Atom {
	var facts []ast.Atom
	for _, sym := range r.store.ListPredicates() {
		if sym.Symbol != word {
			continue
		}
		r.store.GetFacts(ast.NewQuery(sym), func(a ast.Atom) error {
			facts = append(facts, a)
			return nil
		})
	}
	return facts
}

func (r *reader) texts(word string, arity, at int) []string {
	seen := map[string]bool{}
	r.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: word, Arity: arity}), func(a ast.Atom) error {
		seen[key(a.Args[at])] = true
		return nil
	})
	return keys(seen)
}

func (r *reader) pairs(word string) [][2]string {
	var out [][2]string
	r.store.GetFacts(ast.NewQuery(ast.PredicateSym{Symbol: word, Arity: 2}), func(a ast.Atom) error {
		out = append(out, [2]string{key(a.Args[0]), key(a.Args[1])})
		return nil
	})
	return out
}

func (r *reader) notes(item string, findings map[string]bool) []note {
	type place struct {
		word  string
		at    int
		arity int
	}
	grouped := map[place][]string{}
	for _, f := range r.about[item] {
		if len(f.Args) < 2 {
			continue
		}
		for at, arg := range f.Args {
			if key(arg) != item {
				continue
			}
			var others []string
			for k, other := range f.Args {
				if k != at {
					others = append(others, key(other))
				}
			}
			pl := place{f.Predicate.Symbol, at, len(f.Args)}
			grouped[pl] = append(grouped[pl], strings.Join(others, " · "))
		}
	}
	var out []note
	for pl, values := range grouped {
		args := make([]string, pl.arity)
		for k := range args {
			args[k] = "…"
		}
		args[pl.at] = "this"
		out = append(out, note{
			Word:    pl.word,
			Pattern: "(" + strings.Join(args, ", ") + ")",
			Finding: findings[pl.word] && pl.at == 0,
			Values:  sorted(values),
		})
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Finding != out[j].Finding {
			return out[i].Finding
		}
		if out[i].Word != out[j].Word {
			return out[i].Word < out[j].Word
		}
		return out[i].Pattern < out[j].Pattern
	})
	return out
}

func (r *reader) rule(text string) shownRule {
	return shownRule{Text: r.linked(text), Notes: r.notes(text, nil)}
}

func (r *reader) linked(text string) template.HTML {
	links := r.opens[text]
	var b strings.Builder
	esc := template.HTMLEscapeString
	for i := 0; i < len(text); {
		c := text[i]
		if c == '"' || c == '\'' || c == '`' {
			j := i + 1
			for j < len(text) && text[j] != c {
				if text[j] == '\\' && c != '`' {
					j++
				}
				j++
			}
			if j < len(text) {
				j++
			}
			b.WriteString(`<span class="s">` + esc(text[i:j]) + `</span>`)
			i = j
			continue
		}
		if isLower(c) && (i == 0 || !isIdent(text[i-1]) && text[i-1] != ':') {
			j := i
			for j < len(text) && isIdent(text[j]) {
				j++
			}
			name := text[i:j]
			if j < len(text) && text[j] == '(' && links[name] {
				if id, ok := r.wordID[name]; ok {
					b.WriteString(`<a class="word" href="#` + id + `" data-target="` + id + `">` + esc(name) + `</a>`)
				} else {
					b.WriteString(`<span class="word plain">` + esc(name) + `</span>`)
				}
			} else {
				b.WriteString(esc(name))
			}
			i = j
			continue
		}
		b.WriteString(esc(string(c)))
		i++
	}
	return template.HTML(b.String())
}

func isLower(c byte) bool { return c >= 'a' && c <= 'z' }

func isIdent(c byte) bool {
	return isLower(c) || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_'
}

func keys[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func sorted(in []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, s := range in {
		if !seen[s] {
			seen[s] = true
			out = append(out, s)
		}
	}
	sort.Strings(out)
	return out
}

var pageTemplate = template.Must(template.New("page").Parse(`<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{.Title}} conformance</title>
<style>
:root {
  --bg: #f7f6f2; --panel: #ffffff; --ink: #1d1d1b; --muted: #6b6a64; --line: #e3e1d9;
  --code-bg: #f1efe8; --accent: #2f5d8a; --good: #2e7d4f; --good-bg: #e6f3eb;
  --bad: #b3261e; --bad-bg: #fbe9e7; --string: #7a4f12; --chip: #eeece5;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #161614; --panel: #1f1f1c; --ink: #ecebe6; --muted: #a09e95; --line: #34332e;
    --code-bg: #262622; --accent: #8fb8e0; --good: #7fd19f; --good-bg: #1d3226;
    --bad: #f2a29b; --bad-bg: #3a2120; --string: #e2b77a; --chip: #2c2b27;
  }
}
:root[data-theme="dark"] {
  --bg: #161614; --panel: #1f1f1c; --ink: #ecebe6; --muted: #a09e95; --line: #34332e;
  --code-bg: #262622; --accent: #8fb8e0; --good: #7fd19f; --good-bg: #1d3226;
  --bad: #f2a29b; --bad-bg: #3a2120; --string: #e2b77a; --chip: #2c2b27;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink); font: 15px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 980px; margin: 0 auto; padding: 32px 16px 64px; }
header { margin-bottom: 28px; }
h1 { font-size: 26px; margin: 0 0 10px; letter-spacing: -0.01em; }
h2 { font-size: 18px; margin: 36px 0 6px; }
h3 { font-size: 15px; margin: 0; }
p.lead { color: var(--muted); margin: 0 0 14px; }
.verdict { display: inline-flex; gap: 10px; align-items: center; padding: 8px 14px; border-radius: 8px; font-weight: 600; }
.verdict.good { background: var(--good-bg); color: var(--good); }
.verdict.bad { background: var(--bad-bg); color: var(--bad); }
.facts-line { color: var(--muted); font-size: 13px; margin-top: 10px; }
.problems { background: var(--bad-bg); color: var(--bad); border-radius: 8px; padding: 10px 14px; margin-top: 14px; }
.problems li { margin: 2px 0; }
nav.toc { display: flex; flex-wrap: wrap; gap: 8px; margin: 18px 0 0; }
nav.toc a { color: var(--accent); text-decoration: none; font-size: 14px; padding: 4px 10px; border: 1px solid var(--line); border-radius: 999px; background: var(--panel); }
.card { background: var(--panel); border: 1px solid var(--line); border-radius: 10px; padding: 14px 16px; margin: 12px 0; }
.card.flagged { border-color: var(--bad); }
.card .label { color: var(--muted); font-size: 12px; text-transform: uppercase; letter-spacing: 0.06em; margin: 12px 0 4px; }
.rule { background: var(--code-bg); border-radius: 6px; padding: 8px 10px; margin: 6px 0; }
.rule code { font: 13px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre-wrap; overflow-wrap: anywhere; display: block; }
.rule .s { color: var(--string); }
a.word { color: var(--accent); text-decoration: none; border-bottom: 1px dotted var(--accent); cursor: pointer; }
a.word.on { background: var(--accent); color: var(--panel); border-radius: 3px; border-bottom: none; }
.notes { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 6px; }
.chip { background: var(--chip); border-radius: 6px; padding: 2px 8px; font-size: 12px; color: var(--muted); overflow-wrap: anywhere; }
.chip b { color: var(--ink); font-weight: 600; }
.chip.finding { background: var(--bad-bg); color: var(--bad); }
.chip.finding b { color: var(--bad); }
.opened { border-left: 3px solid var(--accent); margin: 8px 0 2px 4px; padding: 2px 0 2px 10px; }
.opened-head { font-size: 12px; color: var(--muted); margin-bottom: 2px; }
.change { padding: 6px 0; border-top: 1px dashed var(--line); }
.change:first-of-type { border-top: none; }
details { background: var(--panel); border: 1px solid var(--line); border-radius: 10px; margin: 8px 0; }
summary { cursor: pointer; padding: 10px 14px; font-weight: 600; }
summary span { color: var(--muted); font-weight: 400; margin-left: 6px; }
details pre { margin: 0; padding: 0 14px 12px; font: 12.5px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre-wrap; overflow-wrap: anywhere; }
.word-card h3 { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.empty { color: var(--muted); font-style: italic; }
</style>
</head>
<body>
<main>
<header>
  <h1>{{.Title}}</h1>
  <p class="lead">What the folder's own program concluded, every rule printed in {{.Language}}.</p>
  <div class="verdict {{if .Good}}good{{else}}bad{{end}}">conforms: {{if .Answer}}{{.Answer}}{{else}}unknown{{end}} <span>· exit {{.Code}}</span></div>
  <div class="facts-line">{{len .Concepts}} concepts · {{len .Words}} words · {{.Rules}} rules shown{{if .Rounds}} · settled in {{.Rounds}} rounds{{end}}</div>
  {{if .Problems}}<ul class="problems">{{range .Problems}}<li>{{.}}</li>{{end}}</ul>{{end}}
  <nav class="toc"><a href="#concepts">Concepts</a><a href="#words">Words</a><a href="#outputs">Outputs</a></nav>
</header>

<h2 id="concepts">Concepts</h2>
<p class="lead">Each concept with the rules that show it and the changes that test it. Click a word in a rule to open the rules that explain it.</p>
{{range .Concepts}}
<section class="card{{if .Flagged}} flagged{{end}}" id="{{.ID}}">
  <h3>{{.Name}}</h3>
  {{if .Notes}}<div class="notes">{{range .Notes}}<span class="chip{{if .Finding}} finding{{end}}"><b>{{.Word}}</b>{{.Pattern}} {{range $i, $v := .Values}}{{if $i}}, {{end}}{{$v}}{{end}}</span>{{end}}</div>{{end}}
  {{if .Rules}}<div class="label">Shown by</div>{{range .Rules}}{{template "rule" .}}{{end}}{{end}}
  {{if .Changes}}<div class="label">Tested by</div>
  {{range .Changes}}<div class="change"><div>{{.Name}}</div>{{if .Notes}}<div class="notes">{{range .Notes}}<span class="chip{{if .Finding}} finding{{end}}"><b>{{.Word}}</b>{{.Pattern}} {{range $i, $v := .Values}}{{if $i}}, {{end}}{{$v}}{{end}}</span>{{end}}</div>{{end}}</div>{{end}}{{end}}
</section>
{{else}}<p class="empty">No concepts were shown.</p>
{{end}}

<h2 id="words">Words</h2>
<p class="lead">Every word that a rule defines, with the rules that explain it.</p>
{{range .Words}}
<section class="card word-card" id="{{.ID}}">
  <h3>{{.Name}}</h3>
  {{if .Notes}}<div class="notes">{{range .Notes}}<span class="chip{{if .Finding}} finding{{end}}"><b>{{.Word}}</b>{{.Pattern}} {{range $i, $v := .Values}}{{if $i}}, {{end}}{{$v}}{{end}}</span>{{end}}</div>{{end}}
  <div class="rules">{{range .Rules}}{{template "rule" .}}{{end}}</div>
</section>
{{else}}<p class="empty">No words were explained.</p>
{{end}}

<h2 id="outputs">Outputs</h2>
<p class="lead">Every fact of every output word, printed in {{.Language}}.</p>
{{range .Outputs}}
<details{{if .Open}} open{{end}}><summary>{{.Word}}<span>{{len .Facts}}</span></summary>{{if .Facts}}<pre>{{range .Facts}}{{.}}
{{end}}</pre>{{else}}<pre class="empty">none</pre>{{end}}</details>
{{end}}
</main>
<script>
document.addEventListener('click', function (e) {
  var a = e.target.closest('a.word');
  if (!a) return;
  var section = document.getElementById(a.dataset.target);
  var host = a.closest('.rule');
  if (!section || !host) return;
  e.preventDefault();
  var key = a.dataset.target;
  var open = null;
  for (var i = 0; i < host.children.length; i++) {
    var c = host.children[i];
    if (c.classList.contains('opened') && c.dataset.key === key) open = c;
  }
  if (open) { open.remove(); a.classList.remove('on'); return; }
  open = document.createElement('div');
  open.className = 'opened';
  open.dataset.key = key;
  var head = document.createElement('div');
  head.className = 'opened-head';
  head.textContent = a.textContent + ' is explained by';
  open.appendChild(head);
  var rules = section.querySelector('.rules');
  if (rules) open.appendChild(rules.cloneNode(true));
  host.appendChild(open);
  a.classList.add('on');
});
</script>
</body>
</html>
{{define "rule"}}<div class="rule"><code>{{.Text}}</code>{{if .Notes}}<div class="notes">{{range .Notes}}<span class="chip{{if .Finding}} finding{{end}}"><b>{{.Word}}</b>{{.Pattern}} {{range $i, $v := .Values}}{{if $i}}, {{end}}{{$v}}{{end}}</span>{{end}}</div>{{end}}</div>{{end}}
`))
