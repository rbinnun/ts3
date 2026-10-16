entry_point("run.me").
spec("spec.mg").
workflow("workflow.mg").
part_of_the_machine("engine.go").
part_of_the_machine("tools.go").
part_of_the_machine("report.go").
part_of_the_machine("run.me").
part_of_the_machine("go.mod").
part_of_the_machine("go.sum").
output_file("report.html").

read_by("does", "engine.go").
read_by("effect", "engine.go").
read_by("gives", "engine.go").
read_by("workflow", "engine.go").
read_by("conforms", "engine.go").
read_by("exit_code", "engine.go").
read_by("output", "report.go").
read_by("output_file", "report.go").
read_by("shows", "report.go").
read_by("shows_change", "report.go").
read_by("opens_into", "report.go").
read_by("explained_by", "report.go").
read_by("printed_in", "report.go").

supplied_by("got", "tools.go").
supplied_by("started_by", "engine.go").
supplied_by("in_the_folder", "workflow.mg").
supplied_by("comment_in", "workflow.mg").
supplied_by("defines", "workflow.mg").
supplied_by("law", "workflow.mg").
supplied_by("within", "workflow.mg").
supplied_by("broke", "workflow.mg").
supplied_by("answered", "workflow.mg").
supplied_by("unfired", "workflow.mg").
supplied_by("size", "workflow.mg").
supplied_by("mentions", "workflow.mg").
supplied_by("law_mentions", "workflow.mg").
supplied_by("rule_for", "workflow.mg").
supplied_by("rule_for_law", "workflow.mg").
supplied_by("rule_uses", "workflow.mg").
supplied_by("rule_in", "workflow.mg").

Decl got(Doing, Field, Value).
Decl started_by(Effect).
Decl in_the_folder(Path).
Decl comment_in(Path, Text).
Decl defines(Path, Predicate).
Decl law(Law).
Decl within(Context).
Decl broke(Change, Law).
Decl answered(Change, Answer).
Decl unfired(Path, Line).
Decl size(Path, Lines).
Decl mentions(Word, Other).
Decl law_mentions(Law, Word).
Decl rule_for(Rule, Word).
Decl rule_for_law(Rule, Law).
Decl rule_uses(Rule, Word).
Decl rule_in(File, Rule).

has_a_role(Path) :- spec(Path).
has_a_role(Path) :- workflow(Path).
has_a_role(Path) :- part_of_the_machine(Path).
has_a_role(Path) :- output_file(Path).

violation("Every file has a role", Path) :- in_the_folder(Path), !has_a_role(Path).

adds_line("a file with no role", "notes.mg", 'note("a").').
must_break("a file with no role", "Every file has a role").

violation("Every workflow is in the folder", Path) :- workflow(Path), !in_the_folder(Path).

adds_line("a missing workflow", "spec.mg", 'workflow("missing.mg").').
must_break("a missing workflow", "Every workflow is in the folder").

violation("Each word has one supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.

adds_line("a workflow that fakes what the tools found", "workflow.mg", 'got("a step", "file", "nowhere").').
must_break("a workflow that fakes what the tools found", "Each word has one supplier").

adds_line("a spec that looks for itself", "spec.mg", 'in_the_folder("ghost.txt").').
must_break("a spec that looks for itself", "Each word has one supplier").

written_in(".mg", "mangle").
written_in(".go", "go").
written_in("go.mod", "go module").
written_in("go.sum", "go checksums").
written_in(".html", "html").
written_in(Entry, "sh") :- entry_point(Entry).
has_comments("mangle").
has_comments("go").
has_comments("sh").

language(Path, Language) :- in_the_folder(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).
known(Path) :- language(Path, _).

violation("The only knowledge is Datalog", Path) :- in_the_folder(Path), !known(Path).
violation("The only knowledge is Datalog", Path) :- comment_in(Path, _).

adds_line("a file that is not datalog", "notes.txt", "a note").
must_break("a file that is not datalog", "The only knowledge is Datalog").

adds_line("a comment", "workflow.mg", "# a note").
must_break("a comment", "The only knowledge is Datalog").

in_a_change() :- within("a change").
change(Change) :- adds_line(Change, _, _).
missed(Change) :- must_break(Change, Law), !broke(Change, Law).
answered_otherwise(Change) :- must_answer(Change, Answer), !answered(Change, Answer).
came_out_as_stated(Change) :- change(Change), !missed(Change), !answered_otherwise(Change).
expects_an_unknown_law(Change) :- must_break(Change, Law), !law(Law).
has_a_counterexample(Law) :- broke(_, Law).
has_a_counterexample(Law) :- in_a_change(), must_break(_, Law).

violation("Every law has a counterexample", Law) :- law(Law), !has_a_counterexample(Law).
violation("Every change comes out as stated", Change) :- change(Change), !in_a_change(), !came_out_as_stated(Change).
violation("Every change comes out as stated", Change) :- expects_an_unknown_law(Change).

adds_line("a law with no counterexample", "workflow.mg", 'violation("A law with no counterexample", Path) :- in_the_folder(Path), :string:ends_with(Path, ".txt").').
must_break("a law with no counterexample", "Every law has a counterexample").

adds_line("a change that expects an unknown law", "workflow.mg", 'must_break("a ghost change", "A law nobody laid down").').
must_break("a change that expects an unknown law", "Every change comes out as stated").

word(Word) :- defines("spec.mg", Word).
word(Word) :- supplied_by(Word, _).
rests_on(Word, Other) :- mentions(Word, Other).
rests_on("violation", Law) :- law(Law).
rests_on("output", Word) :- output(Word).
rests_on(Law, Word) :- law_mentions(Law, Word).
used(Word) :- read_by(Word, _).
used(Other) :- rests_on(Word, Other), used(Word).

violation("Every word is used", Word) :- word(Word), !used(Word).

adds_line("a word nobody uses", "spec.mg", 'lonely("a").').
must_break("a word nobody uses", "Every word is used").

a_law_is_broken() :- violation(_, _).
conforms("false") :- a_law_is_broken().
conforms("true") :- !a_law_is_broken().
exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

adds_line("a spec that cannot load", "spec.mg", "conforms(").
must_answer("a spec that cannot load", "broken").

output("conforms").
output("violation").
output("broke").
output("answered").
output("unfired").
output("size").
output("rests_on").
output("concept").
output("shows").
output("shows_change").
output("opens_into").
output("explained_by").
output("rule_in").
printed_in("mangle").

concept("The folder conforms to the spec").
concept(Law) :- law(Law).
shows("The folder conforms to the spec", Rule) :- rule_for(Rule, "conforms").
shows(Law, Rule) :- concept(Law), rule_for_law(Rule, Law).
shows_change("The folder conforms to the spec", Change) :- must_answer(Change, _).
shows_change(Law, Change) :- concept(Law), must_break(Change, Law).
opens_into(Rule, Word) :- rule_uses(Rule, Word).
explained_by(Word, Rule) :- rule_for(Rule, Word).
