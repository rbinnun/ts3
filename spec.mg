entry_point("run.me").
loads("engine.go", "spec.mg").
loads("engine.go", "workflow.mg").
part_of_the_machine("engine.go").
part_of_the_machine("tools.go").
part_of_the_machine("run.me").
part_of_the_machine("go.mod").
part_of_the_machine("go.sum").

reads_the_word("engine.go", "loads").
reads_the_word("engine.go", "uses").
reads_the_word("engine.go", "conforms").
reads_the_word("engine.go", "exits_with").
reads_the_word("engine.go", "prints").
reads_the_word("engine.go", "prints_in").
reads_the_word("engine.go", "prints_to").
reads_the_word("tools.go", "conforms").
reads_the_word("tools.go", "breaks").
reads_the_word("tools.go", "never_fired").

supplies_the_word("tools.go", "returned").
supplies_the_word("engine.go", "the_kind_of_this_run").
supplies_the_word("engine.go", "a_problem").
supplies_the_word("workflow.mg", "in_the_folder").
supplies_the_word("workflow.mg", "has_the_comment").
supplies_the_word("workflow.mg", "has_lines").
supplies_the_word("workflow.mg", "is_in").
supplies_the_word("workflow.mg", "defines").
supplies_the_word("workflow.mg", "refers_to").
supplies_the_word("workflow.mg", "lays_down").
supplies_the_word("workflow.mg", "broke").
supplies_the_word("workflow.mg", "answered").
supplies_the_word("workflow.mg", "never_fired").

Decl uses(Command, Tool, Input).
Decl returned(Command, Field, Value).
Decl the_kind_of_this_run(Kind).
Decl a_problem(Text).
Decl in_the_folder(File).
Decl has_the_comment(File, Text).
Decl has_lines(File, Count).
Decl is_in(Rule, File).
Decl defines(Rule, Word).
Decl refers_to(Rule, Word).
Decl lays_down(Rule, Law).
Decl broke(Change, Law).
Decl answered(Change, Answer).
Decl never_fired(Rule).

returns("list", "file").
returns("count lines", "lines").
returns("find comments", "comment").
returns("parse", "rule").
returns("read a rule", "word it defines").
returns("read a rule", "law it lays down").
returns("read a rule", "word it refers to").
returns("see what fired", "rule that fired").
returns("try", "conforms").
returns("try", "broke").
returns("try", "never fired").

in_the_catalog(Tool) :- returns(Tool, _).
named_as_a_command(Command) :- uses(Command, _, _), :string:starts_with(Command, "command: ").

breaks(Command, "Every command uses a tool in the catalog") :- uses(Command, Tool, _), !in_the_catalog(Tool).
breaks(Command, "Every command is named as a command") :- uses(Command, _, _), !named_as_a_command(Command).

adds_line("a command with a tool nobody has", "workflow.mg", 'uses("command: guess", "guess", "x").').
must_break("a command with a tool nobody has", "Every command uses a tool in the catalog").

adds_line("a command not named as a command", "workflow.mg", 'uses("list it", "list", "the folder").').
must_break("a command not named as a command", "Every command is named as a command").

given_a_role(File) :- loads(_, File).
given_a_role(File) :- part_of_the_machine(File).

breaks(File, "Every file has a role") :- in_the_folder(File), !given_a_role(File).

adds_line("a file with no role", "notes.mg", 'note("a").').
must_break("a file with no role", "Every file has a role").

breaks(File, "Every file engine.go loads is in the folder") :- loads("engine.go", File), !in_the_folder(File).

adds_line("a missing workflow", "spec.mg", 'loads("engine.go", "missing.mg").').
must_break("a missing workflow", "Every file engine.go loads is in the folder").

has_a_rule_for(File, Word) :- is_in(Rule, File), defines(Rule, Word).

breaks(File, "Each word has one supplier") :- has_a_rule_for(File, Word), supplies_the_word(Supplier, Word), Supplier != File.

adds_line("a workflow that fakes what the tools returned", "workflow.mg", 'returned("command: a fake", "file", "nowhere").').
must_break("a workflow that fakes what the tools returned", "Each word has one supplier").

adds_line("a spec that looks for itself", "spec.mg", 'in_the_folder("ghost.txt").').
must_break("a spec that looks for itself", "Each word has one supplier").

means(".mg", "mangle").
means(".go", "go").
means("go.mod", "go module").
means("go.sum", "go checksums").
means(Entry, "sh") :- entry_point(Entry).
with_comments("mangle").
with_comments("go").
with_comments("sh").

written_in(File, Language) :- in_the_folder(File), means(Ending, Language), :string:ends_with(File, Ending).
known(File) :- written_in(File, _).

breaks(File, "The only knowledge is Datalog") :- in_the_folder(File), !known(File).
breaks(File, "The only knowledge is Datalog") :- has_the_comment(File, _).

adds_line("a file that is not datalog", "notes.txt", "a note").
must_break("a file that is not datalog", "The only knowledge is Datalog").

adds_line("a comment", "workflow.mg", "# a note").
must_break("a comment", "The only knowledge is Datalog").

this_run_is_a_change() :- the_kind_of_this_run("a change").
a_change(Change) :- adds_line(Change, _, _).
missed(Change) :- must_break(Change, Law), !broke(Change, Law).
answered_otherwise(Change) :- must_answer(Change, Answer), !answered(Change, Answer).
as_stated(Change) :- a_change(Change), !missed(Change), !answered_otherwise(Change).
a_law(Law) :- lays_down(_, Law).
about_an_unknown_law(Change) :- must_break(Change, Law), !a_law(Law).
proven(Law) :- broke(_, Law).
proven(Law) :- this_run_is_a_change(), must_break(_, Law).

breaks(Law, "Every law has a counterexample") :- a_law(Law), !proven(Law).
breaks(Change, "Every change comes out as stated") :- a_change(Change), !this_run_is_a_change(), !as_stated(Change).
breaks(Change, "Every change comes out as stated") :- about_an_unknown_law(Change).

adds_line("a law with no counterexample", "workflow.mg", 'breaks(File, "A law with no counterexample") :- in_the_folder(File), :string:ends_with(File, ".txt").').
must_break("a law with no counterexample", "Every law has a counterexample").

adds_line("a change that expects an unknown law", "workflow.mg", 'must_break("a ghost change", "A law nobody laid down").').
must_break("a change that expects an unknown law", "Every change comes out as stated").

a_word(Word) :- has_a_rule_for("spec.mg", Word).
a_word(Word) :- supplies_the_word(_, Word).
rests_on(Word, Other) :- defines(Rule, Word), refers_to(Rule, Other), Word != "breaks".
rests_on(Law, Other) :- lays_down(Rule, Law), refers_to(Rule, Other).
rests_on("breaks", Law) :- a_law(Law).
rests_on("prints", Word) :- prints(_, Word).
used(Word) :- reads_the_word(_, Word).
used(Other) :- rests_on(Word, Other), used(Word).

breaks(Word, "Every word is used") :- a_word(Word), !used(Word).

adds_line("a word nobody uses", "spec.mg", 'lonely("a").').
must_break("a word nobody uses", "Every word is used").

a_law_is_broken() :- breaks(_, _).
conforms("the folder", "false") :- a_law_is_broken().
conforms("the folder", "true") :- !a_law_is_broken().
exits_with("true", 0).
exits_with("false", 1).
exits_with("broken", 2).

adds_line("a spec that cannot load", "spec.mg", "conforms(").
must_answer("a spec that cannot load", "broken").

prints_in("engine.go", "mangle").
prints_to("engine.go", "standard output").
prints("engine.go", "conforms").
prints("engine.go", "breaks").
prints("engine.go", "broke").
prints("engine.go", "answered").
prints("engine.go", "never_fired").
prints("engine.go", "has_lines").
prints("engine.go", "a_problem").
prints("engine.go", "a_concept").
prints("engine.go", "is_made_of").
prints("engine.go", "is_tested_by").
prints("engine.go", "defines").
prints("engine.go", "refers_to").
prints("engine.go", "is_in").
prints("engine.go", "rests_on").

a_concept("The folder conforms to the spec").
a_concept(Law) :- a_law(Law).
is_made_of("The folder conforms to the spec", Rule) :- defines(Rule, "conforms").
is_made_of(Law, Rule) :- lays_down(Rule, Law).
is_tested_by("The folder conforms to the spec", Change) :- must_answer(Change, _).
is_tested_by(Law, Change) :- must_break(Change, Law).
