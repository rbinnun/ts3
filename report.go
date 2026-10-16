package main

import (
	"encoding/json"
	"fmt"
	"html"
	"path/filepath"
	"sort"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/factstore"
	"codeberg.org/TauCeti/mangle-go/parse"
)

func outputsOf(store factstore.FactStore) ([]ast.Atom, error) {
	var outputs []ast.Atom
	for _, atom := range factsNamed(store, "output", 1) {
		name, err := stringOf(atom.Args[0])
		if err != nil {
			return nil, fmt.Errorf("the machinery cannot give the output %v", atom)
		}
		outputs = append(outputs, factsNamed(store, name, -1)...)
	}
	sort.Slice(outputs, func(i, j int) bool { return outputs[i].String() < outputs[j].String() })
	return outputs, nil
}

func printOut(outputs []ast.Atom) []string {
	var printed []string
	for _, atom := range outputs {
		printed = append(printed, atom.String()+".")
	}
	return printed
}

type view struct {
	w       world
	sources map[string]*source
}

type source struct {
	unit   parse.SourceUnit
	places []placed
}

type ruleRef struct {
	key  string
	path string
	line int64
	ok   bool
}

type concept struct {
	name    string
	rules   []ruleRef
	changes []string
}

type ruleData struct {
	Summary string   `json:"summary"`
	Source  string   `json:"source"`
	Words   []string `json:"words"`
}

type wordData struct {
	Summary string   `json:"summary"`
	Rules   []string `json:"rules"`
}

type pageData struct {
	Opens     string              `json:"opens"`
	Explained string              `json:"explained"`
	Rules     map[string]ruleData `json:"rules"`
	Words     map[string]wordData `json:"words"`
}

func written(w world, p *program, store factstore.FactStore, answer ast.Atom) (map[string]string, error) {
	targets := factsNamed(store, "output_file", 1)
	if len(targets) == 0 {
		return nil, nil
	}
	programs := map[string]bool{}
	for _, file := range p.files {
		programs[file] = true
	}
	content, err := render(w, p, store, answer)
	if err != nil {
		return nil, err
	}
	files := map[string]string{}
	for _, atom := range targets {
		path, err := stringOf(atom.Args[0])
		if err != nil {
			return nil, fmt.Errorf("an output file is not named by a string: %v", atom)
		}
		if !filepath.IsLocal(filepath.FromSlash(path)) {
			return nil, fmt.Errorf("the machinery writes only inside the folder, not to %q", path)
		}
		path = filepath.ToSlash(filepath.Clean(filepath.FromSlash(path)))
		if programs[path] {
			return nil, fmt.Errorf("the machinery will not write over the program %s", path)
		}
		files[path] = content
	}
	return files, nil
}

func textOf(c ast.Constant) string {
	if text, err := c.StringValue(); err == nil {
		return text
	}
	return c.DisplayString()
}

func refOf(rule ast.Constant) ruleRef {
	ref := ruleRef{key: rule.DisplayString()}
	if items := listOf(rule); len(items) == 2 {
		path, err1 := items[0].StringValue()
		line, err2 := items[1].NumberValue()
		if err1 == nil && err2 == nil {
			ref = ruleRef{key: fmt.Sprintf("%s:%d", path, line), path: path, line: line, ok: true}
		}
	}
	return ref
}

func before(a, b ruleRef) bool {
	if a.path != b.path {
		return a.path < b.path
	}
	if a.line != b.line {
		return a.line < b.line
	}
	return a.key < b.key
}

func (v *view) source(path string) *source {
	if s, ok := v.sources[path]; ok {
		return s
	}
	var s *source
	if text, ok := v.w[path]; ok {
		if unit, places, err := parseText(text); err == nil {
			s = &source{unit: unit, places: places}
		}
	}
	v.sources[path] = s
	return s
}

func (v *view) clause(ref ruleRef) (ast.Clause, string, bool) {
	if !ref.ok {
		return ast.Clause{}, "", false
	}
	s := v.source(ref.path)
	if s == nil {
		return ast.Clause{}, "", false
	}
	for i, place := range s.places {
		if int64(place.line) == ref.line {
			return s.unit.Clauses[i], place.text, true
		}
	}
	return ast.Clause{}, "", false
}

func codeHTML(text string) string {
	return "<code>" + html.EscapeString(text) + "</code>"
}

func premiseHTML(t ast.Term) string {
	if negated, ok := t.(ast.NegAtom); ok {
		return codeHTML("!" + negated.Atom.String())
	}
	return codeHTML(t.String())
}

func sentence(c ast.Clause) string {
	text := codeHTML(c.Head.String())
	for i, premise := range c.Premises {
		join := "and"
		if i == 0 {
			join = "when"
		}
		text += ` <span class="join">` + join + `</span> ` + premiseHTML(premise)
	}
	if c.Transform != nil {
		text += " " + codeHTML("|> "+c.Transform.String())
	}
	return text
}

func (v *view) rule(ref ruleRef, words []string) ruleData {
	data := ruleData{Summary: `<span class="sentence">` + html.EscapeString(ref.key) + "</span>", Words: words}
	if clause, text, ok := v.clause(ref); ok {
		data.Summary = `<span class="sentence">` + sentence(clause) + `</span><span class="site">` + html.EscapeString(ref.key) + "</span>"
		data.Source = text
	}
	return data
}

func wordHTML(name string) string {
	return `<span class="sentence"><code class="word">` + html.EscapeString(name) + "</code></span>"
}

func render(w world, p *program, store factstore.FactStore, answer ast.Atom) (string, error) {
	v := &view{w: w, sources: map[string]*source{}}
	refs := map[string]ruleRef{}
	note := func(rule ast.Constant) ruleRef {
		ref := refOf(rule)
		refs[ref.key] = ref
		return ref
	}
	opens := map[string]map[string]bool{}
	explains := map[string]map[string]bool{}
	for _, atom := range factsNamed(store, "opens_into", 2) {
		ref := note(constantOf(atom.Args[0]))
		word := textOf(constantOf(atom.Args[1]))
		if opens[ref.key] == nil {
			opens[ref.key] = map[string]bool{}
		}
		opens[ref.key][word] = true
		if explains[word] == nil {
			explains[word] = map[string]bool{}
		}
	}
	for _, atom := range factsNamed(store, "explained_by", 2) {
		word := textOf(constantOf(atom.Args[0]))
		ref := note(constantOf(atom.Args[1]))
		if explains[word] == nil {
			explains[word] = map[string]bool{}
		}
		explains[word][ref.key] = true
	}
	concepts := map[string]*concept{}
	conceptOf := func(term ast.BaseTerm) *concept {
		name := textOf(constantOf(term))
		if concepts[name] == nil {
			concepts[name] = &concept{name: name}
		}
		return concepts[name]
	}
	for _, atom := range factsNamed(store, "shows", 2) {
		c := conceptOf(atom.Args[0])
		c.rules = append(c.rules, note(constantOf(atom.Args[1])))
	}
	for _, atom := range factsNamed(store, "shows_change", 2) {
		c := conceptOf(atom.Args[0])
		c.changes = append(c.changes, textOf(constantOf(atom.Args[1])))
	}
	data := pageData{
		Opens:     "opens_into",
		Explained: "explained_by",
		Rules:     map[string]ruleData{},
		Words:     map[string]wordData{},
	}
	for key, ref := range refs {
		words := []string{}
		for word := range opens[key] {
			words = append(words, word)
		}
		sort.Strings(words)
		data.Rules[key] = v.rule(ref, words)
	}
	for word, keys := range explains {
		var listed []ruleRef
		for key := range keys {
			listed = append(listed, refs[key])
		}
		sort.Slice(listed, func(i, j int) bool { return before(listed[i], listed[j]) })
		rules := []string{}
		for _, ref := range listed {
			rules = append(rules, ref.key)
		}
		data.Words[word] = wordData{Summary: wordHTML(word), Rules: rules}
	}
	var ordered []*concept
	for _, c := range concepts {
		sort.Strings(c.changes)
		sort.Slice(c.rules, func(i, j int) bool { return before(c.rules[i], c.rules[j]) })
		ordered = append(ordered, c)
	}
	rank := func(c *concept) int {
		for _, ref := range c.rules {
			if clause, _, ok := v.clause(ref); ok && clause.Head.Predicate.Symbol == answer.Predicate.Symbol {
				return 0
			}
		}
		if len(c.rules) > 0 {
			return 1
		}
		return 2
	}
	sort.Slice(ordered, func(i, j int) bool {
		a, b := ordered[i], ordered[j]
		if ra, rb := rank(a), rank(b); ra != rb {
			return ra < rb
		}
		if len(a.rules) > 0 && len(b.rules) > 0 && a.rules[0].key != b.rules[0].key {
			return before(a.rules[0], b.rules[0])
		}
		return a.name < b.name
	})
	encoded, err := json.Marshal(data)
	if err != nil {
		return "", fmt.Errorf("the report cannot be written: %w", err)
	}
	start := ""
	if len(p.files) > 0 {
		start = p.files[0]
	}
	var b []byte
	b = append(b, "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"...)
	b = fmt.Appendf(b, "<title>%s</title>\n<style>\n%s</style>\n</head>\n<body>\n<main>\n<header>\n", html.EscapeString(start), pageStyle)
	b = fmt.Appendf(b, "<p class=\"origin\">%s</p>\n<h1>%s</h1>\n", html.EscapeString(start), codeHTML(answer.String()))
	if len(ordered) > 0 {
		b = append(b, "<nav>\n"...)
		for i, c := range ordered {
			b = fmt.Appendf(b, "<a href=\"#concept-%d\">%s</a>\n", i+1, html.EscapeString(c.name))
		}
		b = append(b, "</nav>\n"...)
	}
	b = append(b, "</header>\n"...)
	for i, c := range ordered {
		b = fmt.Appendf(b, "<section class=\"concept\" id=\"concept-%d\">\n<h2>%s</h2>\n", i+1, html.EscapeString(c.name))
		if len(c.rules) > 0 {
			b = append(b, "<p class=\"label\">shows</p>\n<ul class=\"tree\">\n"...)
			for _, ref := range c.rules {
				b = fmt.Appendf(b, "<li><details class=\"rule\" data-rule=\"%s\"><summary>%s</summary></details></li>\n", html.EscapeString(ref.key), data.Rules[ref.key].Summary)
			}
			b = append(b, "</ul>\n"...)
		}
		if len(c.changes) > 0 {
			b = append(b, "<p class=\"label\">shows_change</p>\n<ul class=\"changes\">\n"...)
			for _, name := range c.changes {
				b = fmt.Appendf(b, "<li>%s</li>\n", html.EscapeString(name))
			}
			b = append(b, "</ul>\n"...)
		}
		b = append(b, "</section>\n"...)
	}
	b = fmt.Appendf(b, "</main>\n<script type=\"application/json\" id=\"report-data\">%s</script>\n<script>\n%s</script>\n</body>\n</html>\n", encoded, pageScript)
	return string(b), nil
}

const pageStyle = `:root {
  --bg: #f6f5f1;
  --card: #ffffff;
  --ink: #1f1e1b;
  --muted: #6c6a63;
  --line: #e2dfd6;
  --accent: #2b5983;
  --code: #efede6;
  --again: #9a6c12;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #151514;
    --card: #1e1e1c;
    --ink: #ecebe6;
    --muted: #9d9b93;
    --line: #34332f;
    --accent: #8fb8de;
    --code: #2a2926;
    --again: #d9ad55;
    color-scheme: dark;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink); font: 16px/1.55 ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
main { max-width: 54rem; margin: 0 auto; padding: 2.5rem 1rem 4rem; }
header { margin-bottom: 2rem; }
.origin { margin: 0; font: 0.85rem ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color: var(--muted); }
h1 { margin: 0.3rem 0 1.25rem; font-size: 1.8rem; line-height: 1.2; font-weight: 650; }
h1 code { background: none; padding: 0; font-size: 1em; }
nav { display: flex; flex-wrap: wrap; gap: 0.4rem; }
nav a { color: var(--accent); text-decoration: none; background: var(--card); border: 1px solid var(--line); border-radius: 999px; padding: 0.15rem 0.7rem; font-size: 0.85rem; }
nav a:hover { border-color: var(--accent); }
.concept { background: var(--card); border: 1px solid var(--line); border-radius: 12px; padding: 1.25rem 1.25rem 1rem; margin: 0 0 1.25rem; scroll-margin-top: 1rem; }
h2 { margin: 0; font-size: 1.3rem; line-height: 1.3; }
.label { margin: 1rem 0 0.3rem; font: 600 0.75rem ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color: var(--muted); }
.body > .label { margin-top: 0.55rem; }
ul.tree { list-style: none; margin: 0; padding: 0; }
.body { margin: 0.1rem 0 0.5rem 0.6rem; padding-left: 0.9rem; border-left: 2px solid var(--line); }
summary { display: flex; gap: 0.75rem; align-items: baseline; cursor: pointer; list-style: none; padding: 0.3rem 0.45rem; border-radius: 6px; }
summary::-webkit-details-marker { display: none; }
summary::before { content: "\25B8"; flex: none; color: var(--muted); transition: transform 0.15s; }
details[open] > summary::before { transform: rotate(90deg); }
summary:hover { background: var(--code); }
.leaf { padding: 0.3rem 0.45rem 0.3rem 1.6rem; }
.sentence { flex: 1; min-width: 0; }
.site { flex: none; font: 0.75rem ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; color: var(--muted); }
.join { color: var(--muted); font-style: italic; }
code { font: 0.85em ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; background: var(--code); border-radius: 4px; padding: 0.05rem 0.3rem; overflow-wrap: anywhere; }
code.word { color: var(--accent); }
pre.source { margin: 0.3rem 0 0.2rem; padding: 0.5rem 0.7rem; background: var(--code); border-radius: 6px; font: 0.8rem/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre-wrap; overflow-wrap: anywhere; }
.again > summary { color: var(--again); }
.again > summary::after { content: "\21BA"; flex: none; color: var(--again); }
ul.changes { display: flex; flex-wrap: wrap; gap: 0.4rem; list-style: none; margin: 0; padding: 0; }
ul.changes li { background: var(--code); border-radius: 6px; padding: 0.15rem 0.6rem; font-size: 0.9rem; }
@media (max-width: 36rem) {
  main { padding: 1.5rem 1rem 3rem; }
  h1 { font-size: 1.4rem; }
  .concept { padding: 1rem 0.85rem 0.75rem; }
  summary { flex-wrap: wrap; row-gap: 0.1rem; }
  .site { width: 100%; padding-left: 1.4rem; }
}
`

const pageScript = `(function () {
  var data = JSON.parse(document.getElementById("report-data").textContent);
  function make(tag, className, markup) {
    var node = document.createElement(tag);
    if (className) node.className = className;
    if (markup) node.innerHTML = markup;
    return node;
  }
  function again(node, attribute, value) {
    for (var up = node.parentElement; up; up = up.parentElement) {
      if (up.getAttribute(attribute) === value) return true;
    }
    return false;
  }
  function ruleNode(key) {
    var details = make("details", "rule");
    details.setAttribute("data-rule", key);
    var summary = make("summary");
    if (data.rules[key]) summary.innerHTML = data.rules[key].summary;
    else summary.textContent = key;
    details.appendChild(summary);
    return details;
  }
  function wordNode(name) {
    var word = data.words[name];
    if (!word || word.rules.length === 0) {
      var leaf = make("div", "leaf");
      if (word) leaf.innerHTML = word.summary;
      else leaf.textContent = name;
      return leaf;
    }
    var details = make("details", "word");
    details.setAttribute("data-word", name);
    details.appendChild(make("summary", "", word.summary));
    return details;
  }
  function list(items, build) {
    var ul = make("ul", "tree");
    items.forEach(function (item) {
      var li = make("li");
      li.appendChild(build(item));
      ul.appendChild(li);
    });
    return ul;
  }
  function fill(details) {
    if (details.hasAttribute("data-filled")) return;
    details.setAttribute("data-filled", "");
    var body = make("div", "body");
    if (details.hasAttribute("data-rule")) {
      var key = details.getAttribute("data-rule");
      var rule = data.rules[key];
      if (again(details, "data-rule", key)) details.classList.add("again");
      if (rule && rule.source) {
        var pre = make("pre", "source");
        pre.textContent = rule.source;
        body.appendChild(pre);
      }
      if (rule && rule.words.length) {
        body.appendChild(make("p", "label", data.opens));
        body.appendChild(list(rule.words, wordNode));
      }
    } else {
      var name = details.getAttribute("data-word");
      var word = data.words[name];
      if (again(details, "data-word", name)) details.classList.add("again");
      body.appendChild(make("p", "label", data.explained));
      body.appendChild(list(word ? word.rules : [], ruleNode));
    }
    details.appendChild(body);
  }
  document.addEventListener("toggle", function (event) {
    var target = event.target;
    if (target instanceof HTMLDetailsElement && target.open) fill(target);
  }, true);
})();
`
