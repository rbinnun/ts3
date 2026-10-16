mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
machine_program("machine.mg").

leg("universe.mg").
leg("machine.mg").
leg("the machinery").
source_of_truth("universe.mg").
written_by("universe.mg", "the owner").
written_by("machine.mg", "the builder").
written_by("the machinery", "the builder").

read_by_the_machinery("does").
read_by_the_machinery("effect").
read_by_the_machinery("gives").
read_by_the_machinery("machine_program").
read_by_the_machinery("output").
read_by_the_machinery("answer").
read_by_the_machinery("exit_code").

supplied_by("got", "the machinery").
supplied_by("started_by", "the machinery").
supplied_by("universe_file", "machine.mg").
supplied_by("comment_in", "machine.mg").
supplied_by("defines", "machine.mg").
supplied_by("law", "machine.mg").
supplied_by("within", "machine.mg").
supplied_by("case_broke", "machine.mg").
supplied_by("case_answered", "machine.mg").
supplied_by("unfired", "machine.mg").
supplied_by("size", "machine.mg").

Decl got(Doing, Field, Value).
Decl started_by(Effect).
Decl universe_file(Path).
Decl comment_in(Path, Text).
Decl defines(Path, Predicate).
Decl law(Law).
Decl within(Context).
Decl case_broke(Case, Law).
Decl case_answered(Case, Answer).
Decl unfired(Path, Line).
Decl size(Path, Lines).

written_in(".mg", "mangle").
written_in(".go", "go").
written_in("go.mod", "go module").
written_in("go.sum", "go checksums").
written_in(Entry, "sh") :- entry_point(Entry).
readable("mangle").
has_comments("mangle").
has_comments("go").
has_comments("sh").

output("answer", "mangle").
output("violation", "mangle").
output("case_broke", "mangle").
output("case_answered", "mangle").
output("unfired", "mangle").
output("size", "mangle").

exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).
known(Path) :- language(Path, _).

belongs_to("universe.mg", "universe.mg").
belongs_to(Path, "machine.mg") :- machine_program(Path).
belongs_to(Path, "the machinery") :- language(Path, Language), !readable(Language).
in_a_leg(Path) :- belongs_to(Path, Leg), leg(Leg).

in_a_case() :- within("a case").
case(Case) :- case_answer(Case, _).
missed(Case) :- case_expects(Case, Law), !case_broke(Case, Law).
came_out_as_stated(Case) :- case_answer(Case, Answer), case_answered(Case, Answer), !missed(Case).
expects_no_law(Case) :- case_expects(Case, Law), !law(Law).
shown_failing(Law) :- case_broke(_, Law).
shown_failing(Law) :- in_a_case(), case_expects(_, Law).

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).
violation("the_only_knowledge_is_datalog", Path) :- comment_in(Path, _).
violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.
violation("every_file_belongs_to_a_leg", Path) :- universe_file(Path), !in_a_leg(Path).
violation("the_world_sees_itself", "universe.mg") :- !universe_file("universe.mg").
violation("the_world_sees_itself", Path) :- machine_program(Path), !universe_file(Path).
violation("every_law_is_shown_failing", Law) :- law(Law), !shown_failing(Law).
violation("every_case_comes_out_as_stated", Case) :- case(Case), !in_a_case(), !came_out_as_stated(Case).
violation("every_case_comes_out_as_stated", Case) :- expects_no_law(Case).

a_law_is_broken() :- violation(_, _).
answer("false") :- a_law_is_broken().
answer("true") :- !a_law_is_broken().

case_answer("the world as it stands", "true").

case_adds_line("a file that is not datalog", "notes.txt", "a note").
case_expects("a file that is not datalog", "the_only_knowledge_is_datalog").
case_answer("a file that is not datalog", "false").

case_adds_line("a comment", "machine.mg", "# a note").
case_expects("a comment", "the_only_knowledge_is_datalog").
case_answer("a comment", "false").

case_adds_line("a program that fakes an observation", "machine.mg", 'got("a step", "file", "nowhere").').
case_expects("a program that fakes an observation", "each_word_has_one_supplier").
case_answer("a program that fakes an observation", "false").

case_adds_line("a spec that observes for itself", "universe.mg", 'universe_file("ghost.txt").').
case_expects("a spec that observes for itself", "each_word_has_one_supplier").
case_answer("a spec that observes for itself", "false").

case_adds_line("a file outside the legs", "notes.mg", 'note("a").').
case_expects("a file outside the legs", "every_file_belongs_to_a_leg").
case_answer("a file outside the legs", "false").

case_adds_line("a machine program that is missing", "universe.mg", 'machine_program("missing.mg").').
case_expects("a machine program that is missing", "the_world_sees_itself").
case_answer("a machine program that is missing", "false").

case_adds_line("a law with no case", "machine.mg", 'violation("a_law_with_no_case", Path) :- universe_file(Path), :string:ends_with(Path, ".txt").').
case_expects("a law with no case", "every_law_is_shown_failing").
case_answer("a law with no case", "false").

case_adds_line("a case that expects a law nobody laid down", "machine.mg", 'case_expects("a ghost case", "a_law_nobody_laid_down").').
case_expects("a case that expects a law nobody laid down", "every_case_comes_out_as_stated").
case_answer("a case that expects a law nobody laid down", "false").

case_adds_line("a world that cannot load", "universe.mg", "answer(").
case_answer("a world that cannot load", "broken").
