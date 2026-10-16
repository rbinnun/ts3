package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"codeberg.org/TauCeti/mangle-go/ast"
)

type concept struct {
	Name    string   `json:"name"`
	Rules   []string `json:"rules"`
	Changes []string `json:"changes"`
}

type table struct {
	Name string  `json:"name"`
	Rows [][]any `json:"rows"`
}

type page struct {
	Answer    string              `json:"answer"`
	Problems  []string            `json:"problems"`
	Concepts  []concept           `json:"concepts"`
	OpensInto map[string][]string `json:"opensInto"`
	Explained map[string][]string `json:"explained"`
	Outputs   []table             `json:"outputs"`
}

func plain(c ast.Constant) any {
	switch c.Type {
	case ast.StringType:
		s, _ := c.StringValue()
		return s
	case ast.NumberType:
		n, _ := c.NumberValue()
		return n
	case ast.PairShape:
		fst, snd, _ := c.PairValue()
		return []any{plain(fst), plain(snd)}
	case ast.ListShape:
		items := []any{}
		if seq, err := c.ListSeq(); err == nil {
			for item := range seq {
				items = append(items, plain(item))
			}
		}
		return items
	}
	return c.String()
}

func (r *run) outputs() []table {
	tables := []table{}
	for _, name := range r.full.column("output") {
		t := table{Name: name, Rows: [][]any{}}
		for _, row := range r.full.facts(name) {
			cells := make([]any, len(row))
			for i, c := range row {
				cells[i] = plain(c)
			}
			t.Rows = append(t.Rows, cells)
		}
		tables = append(tables, t)
	}
	return tables
}

func (r *run) pairs(name string) map[string][]string {
	out := map[string][]string{}
	for _, row := range r.full.facts(name) {
		if len(row) != 2 {
			continue
		}
		key, err1 := text(row[0])
		value, err2 := text(row[1])
		if err1 == nil && err2 == nil {
			out[key] = append(out[key], value)
		}
	}
	return out
}

func (r *run) page() page {
	p := page{
		Answer:    r.answer,
		Problems:  append([]string{}, r.problems...),
		Concepts:  []concept{},
		OpensInto: r.pairs("opens_into"),
		Explained: r.pairs("explained_by"),
		Outputs:   r.outputs(),
	}
	shows, changes := r.pairs("shows"), r.pairs("shows_change")
	names := map[string]bool{}
	for name := range shows {
		names[name] = true
	}
	for name := range changes {
		names[name] = true
	}
	for name := range names {
		p.Concepts = append(p.Concepts, concept{name, append([]string{}, shows[name]...), append([]string{}, changes[name]...)})
	}
	sort.Slice(p.Concepts, func(i, j int) bool { return p.Concepts[i].Name < p.Concepts[j].Name })
	return p
}

var printers = map[string]func(r *run) string{
	"json":   (*run).inJSON,
	"mangle": (*run).inMangle,
}

func (m *model) printer() (func(r *run) string, error) {
	languages := m.column("printed_in")
	switch {
	case len(languages) == 0:
		return (*run).inJSON, nil
	case len(languages) > 1:
		return (*run).inJSON, fmt.Errorf("the spec asks for the output printed in %d languages instead of one: %v", len(languages), languages)
	}
	say, ok := printers[languages[0]]
	if !ok {
		return (*run).inJSON, fmt.Errorf("there is no way to print the output in %s", languages[0])
	}
	return say, nil
}

func (r *run) inJSON() string {
	compact := func(v any) string {
		b, _ := json.Marshal(v)
		return string(b)
	}
	var said strings.Builder
	fmt.Fprintf(&said, "{\n  \"answer\": %s,\n  \"problems\": %s,\n  \"facts\": {", compact(r.answer), compact(append([]string{}, r.problems...)))
	if r.answer != "broken" {
		for i, t := range r.outputs() {
			if i > 0 {
				said.WriteString(",")
			}
			fmt.Fprintf(&said, "\n    %s: [", compact(t.Name))
			for j, row := range t.Rows {
				if j > 0 {
					said.WriteString(",")
				}
				said.WriteString("\n      " + compact(row))
			}
			if len(t.Rows) > 0 {
				said.WriteString("\n    ")
			}
			said.WriteString("]")
		}
		said.WriteString("\n  ")
	}
	said.WriteString("}\n}\n")
	return said.String()
}

func mangle(c ast.Constant) string {
	if s, err := text(c); err == nil {
		return ast.String(strings.ToValidUTF8(s, "\uFFFD")).String()
	}
	return c.String()
}

func (r *run) inMangle() string {
	var said strings.Builder
	fact := func(name string, args ...ast.Constant) {
		parts := make([]string, len(args))
		for i, arg := range args {
			parts[i] = mangle(arg)
		}
		fmt.Fprintf(&said, "%s(%s).\n", name, strings.Join(parts, ", "))
	}
	fact("answer", ast.String(r.answer))
	for _, problem := range r.problems {
		fact("problem", ast.String(problem))
	}
	if r.answer != "broken" {
		for _, name := range r.full.column("output") {
			said.WriteString("\n")
			for _, row := range r.full.facts(name) {
				fact(name, row...)
			}
		}
	}
	return said.String()
}

func (r *run) tell() {
	best := r.full
	if best == nil {
		best = r.stated
	}
	say, err := best.printer()
	if err != nil {
		r.fail("%v", err)
		r.answer = "broken"
	}
	fmt.Print(say(r))
	for _, problem := range r.problems {
		fmt.Fprintln(os.Stderr, problem)
	}
	files := best.column("output_file")
	if len(files) == 0 {
		fmt.Fprintln(os.Stderr, "the spec names no output file, so no report was written")
		return
	}
	shown := r
	if r.answer == "broken" {
		shown = &run{answer: r.answer, problems: r.problems}
	}
	data, err := json.Marshal(shown.page())
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return
	}
	html := strings.Replace(reportPage, "DATA", string(data), 1)
	for _, file := range files {
		if err := os.WriteFile(filepath.Join(r.folder, file), []byte(html), 0o644); err != nil {
			fmt.Fprintln(os.Stderr, err)
		}
	}
}

const reportPage = `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Spec Check</title>
<style>
:root {
  --bg: #f7f6f2; --panel: #ffffff; --ink: #1d1d1b; --muted: #6b6a64; --line: #e3e1d9;
  --code-bg: #f1efe8; --chip: #ebe8de; --chip-ink: #3a3933;
  --good: #1f7a4a; --good-bg: #e2f3e9; --bad: #b3261e; --bad-bg: #fbe5e3; --warn: #8a5a00; --warn-bg: #fbefd6;
  --accent: #3355aa;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #161614; --panel: #1f1f1c; --ink: #ecebe6; --muted: #a09f97; --line: #34332e;
    --code-bg: #2a2a26; --chip: #33322d; --chip-ink: #e2e0d8;
    --good: #6fd09a; --good-bg: #183526; --bad: #ff8a80; --bad-bg: #3d1b18; --warn: #f0c060; --warn-bg: #3a2e12;
    --accent: #8fa8ff;
  }
}
:root[data-theme="dark"] {
  --bg: #161614; --panel: #1f1f1c; --ink: #ecebe6; --muted: #a09f97; --line: #34332e;
  --code-bg: #2a2a26; --chip: #33322d; --chip-ink: #e2e0d8;
  --good: #6fd09a; --good-bg: #183526; --bad: #ff8a80; --bad-bg: #3d1b18; --warn: #f0c060; --warn-bg: #3a2e12;
  --accent: #8fa8ff;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink); font: 15px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 1040px; margin: 0 auto; padding: 32px 16px 64px; }
h1 { font-size: 26px; margin: 0 0 6px; }
h2 { font-size: 19px; margin: 40px 0 12px; }
h3 { font-size: 16px; margin: 0 0 10px; }
.lede { color: var(--muted); margin: 0 0 20px; }
.answer { display: inline-flex; align-items: center; gap: 10px; padding: 10px 16px; border-radius: 10px; font-weight: 600; font-size: 17px; }
.answer.true { background: var(--good-bg); color: var(--good); }
.answer.false { background: var(--bad-bg); color: var(--bad); }
.answer.broken { background: var(--warn-bg); color: var(--warn); }
.problems { margin: 16px 0 0; padding-left: 20px; color: var(--warn); }
.card { background: var(--panel); border: 1px solid var(--line); border-radius: 12px; padding: 16px; margin: 0 0 14px; }
.label { font-size: 12px; text-transform: uppercase; letter-spacing: .06em; color: var(--muted); margin: 12px 0 6px; }
.rule { margin: 6px 0; }
code, .code { font: 13px/1.45 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.code { display: block; background: var(--code-bg); border-radius: 8px; padding: 8px 10px; overflow-x: auto; white-space: pre-wrap; word-break: break-word; }
.words { display: flex; flex-wrap: wrap; gap: 6px; margin: 6px 0 0; }
button.word { border: 1px solid var(--line); background: var(--chip); color: var(--chip-ink); border-radius: 999px; padding: 2px 10px; font: 12px ui-monospace, Menlo, monospace; cursor: pointer; }
button.word[aria-expanded="true"] { border-color: var(--accent); color: var(--accent); }
.nest { margin: 8px 0 4px 14px; padding-left: 12px; border-left: 2px solid var(--line); }
.empty { color: var(--muted); font-style: italic; font-size: 13px; }
ul.changes { margin: 0; padding-left: 18px; }
ul.changes li { margin: 4px 0; }
.mention { color: var(--muted); font-size: 13px; }
.table-wrap { overflow-x: auto; background: var(--panel); border: 1px solid var(--line); border-radius: 12px; margin: 0 0 14px; }
table { border-collapse: collapse; width: 100%; font-size: 13px; }
caption { text-align: left; padding: 12px 14px 4px; font-weight: 600; }
th, td { text-align: left; padding: 6px 14px; border-top: 1px solid var(--line); vertical-align: top; }
td { font-family: ui-monospace, Menlo, monospace; word-break: break-word; }
td.num { text-align: right; }
</style>
</head>
<body>
<main>
<h1>Spec check</h1>
<p class="lede">What the folder says about itself, read from the outputs the spec names.</p>
<div id="answer"></div>
<ul class="problems" id="problems"></ul>
<h2>Concepts</h2>
<div id="concepts"></div>
<h2>Outputs</h2>
<div id="outputs"></div>
</main>
<script>
const data = DATA;
const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text !== undefined) e.textContent = text; return e; };
const cell = v => Array.isArray(v) ? v.map(cell).join(" → ") : String(v);

const answer = el("div", "answer " + data.answer, "conforms: " + data.answer);
document.getElementById("answer").appendChild(answer);
for (const p of data.problems || []) document.getElementById("problems").appendChild(el("li", "", p));

function ruleBlock(rule) {
  const box = el("div", "rule");
  box.appendChild(el("code", "code", rule));
  const words = data.opensInto[rule] || [];
  if (!words.length) return box;
  const row = el("div", "words");
  const nest = el("div");
  for (const word of words) {
    const b = el("button", "word", word);
    b.type = "button";
    b.setAttribute("aria-expanded", "false");
    let open = null;
    b.addEventListener("click", () => {
      if (open) { open.remove(); open = null; b.setAttribute("aria-expanded", "false"); return; }
      open = el("div", "nest");
      const rules = data.explained[word] || [];
      if (!rules.length) open.appendChild(el("div", "empty", word + " has no rules here: its facts come from outside the rules."));
      for (const r of rules) open.appendChild(ruleBlock(r));
      nest.appendChild(open);
      b.setAttribute("aria-expanded", "true");
    });
    row.appendChild(b);
  }
  box.appendChild(row);
  box.appendChild(nest);
  return box;
}

function mentions(value) {
  const out = [];
  for (const t of data.outputs) for (const row of t.rows) if (row.some(v => v === value)) out.push(t.name + "(" + row.map(cell).join(", ") + ")");
  return out;
}

const concepts = document.getElementById("concepts");
if (!data.concepts.length) concepts.appendChild(el("p", "empty", "No concepts to show."));
for (const c of data.concepts) {
  const card = el("section", "card");
  card.appendChild(el("h3", "", c.name));
  const seen = mentions(c.name);
  if (seen.length) { card.appendChild(el("div", "label", "In the outputs")); for (const m of seen) card.appendChild(el("div", "mention", m)); }
  card.appendChild(el("div", "label", "Shown by"));
  if (!c.rules.length) card.appendChild(el("div", "empty", "No rule shows this."));
  for (const r of c.rules) card.appendChild(ruleBlock(r));
  card.appendChild(el("div", "label", "Changes that should show it"));
  if (!c.changes.length) card.appendChild(el("div", "empty", "No change."));
  const ul = el("ul", "changes");
  for (const ch of c.changes) {
    const li = el("li", "", ch);
    for (const m of mentions(ch)) { li.appendChild(document.createElement("br")); li.appendChild(el("span", "mention", m)); }
    ul.appendChild(li);
  }
  card.appendChild(ul);
  concepts.appendChild(card);
}

const outputs = document.getElementById("outputs");
if (!data.outputs.length) outputs.appendChild(el("p", "empty", "No outputs."));
for (const t of data.outputs) {
  const wrap = el("div", "table-wrap");
  const table = el("table");
  table.appendChild(el("caption", "", t.name + " (" + t.rows.length + ")"));
  for (const row of t.rows) {
    const tr = el("tr");
    for (const v of row) tr.appendChild(el("td", typeof v === "number" ? "num" : "", cell(v)));
    table.appendChild(tr);
  }
  if (!t.rows.length) { const tr = el("tr"); tr.appendChild(el("td", "empty", "none")); table.appendChild(tr); }
  wrap.appendChild(table);
  outputs.appendChild(wrap);
}
</script>
</body>
</html>
`
