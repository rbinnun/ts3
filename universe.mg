mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
machine_program("machine.mg").

leg("universe.mg").
leg("machine.mg").
leg("the machinery").
rebuilt_from(Leg, Other) :- leg(Leg), leg(Other), Leg != Other.
source_of_truth("universe.mg").
a_rebuild_replaces(Leg) :- leg(Leg), !source_of_truth(Leg).
a_rebuild_proposes(Leg) :- source_of_truth(Leg).
written_by("universe.mg", "the owner").
written_by("machine.mg", "the builder").
written_by("the machinery", "the builder").

written_in(".mg", "mangle").
written_in(".go", "go").
written_in("go.mod", "go module").
written_in("go.sum", "go checksums").
written_in(Entry, "sh") :- entry_point(Entry).
readable("mangle").
has_comments("mangle").
has_comments("go").
has_comments("sh").

supplied_by("got", "the machine").
supplied_by("about", "machine.mg").
supplied_by("met_by", "machine.mg").
supplied_by("serves", "machine.mg").
supplied_by("started_by", "the machine").

output("tells", "mangle").
output("violation", "mangle").

exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

Decl got(Doing, Field, Value).
Decl about(Text, Requirement).
Decl met_by(Requirement, Doing).
Decl serves(Requirement, Purpose).
Decl started_by(Effect).

does("list the universe").
effect("list the universe", "list_a_folder").
gives("list the universe", "folder", ".").

universe_file(Path) :- got("list the universe", "file", Path).
tells(Path) :- universe_file(Path).

language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).
known(Path) :- language(Path, _).
datalog(Path) :- language(Path, Language), readable(Language).

finding_comments(Doing, Path) :- language(Path, Language), has_comments(Language), Doing = fn:string:concat("find comments in ", Path).
does(Doing) :- finding_comments(Doing, _).
effect(Doing, "find_comments") :- finding_comments(Doing, _).
gives(Doing, "path", Path) :- finding_comments(Doing, Path).
gives(Doing, "language", Language) :- finding_comments(Doing, Path), language(Path, Language).

reading_a_program(Doing, Path) :- datalog(Path), Doing = fn:string:concat("read the program ", Path).
does(Doing) :- reading_a_program(Doing, _).
effect(Doing, "read_a_program") :- reading_a_program(Doing, _).
gives(Doing, "path", Path) :- reading_a_program(Doing, Path).
defines(Path, Predicate) :- reading_a_program(Doing, Path), got(Doing, "defines", Predicate).
law(Law) :- reading_a_program(Doing, _), got(Doing, "law", Law).

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).
violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).
violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.

does("read the universe").
effect("read the universe", "read_lines").
gives("read the universe", "path", "universe.mg").

universe_line(Text) :- got("read the universe", "line", Text), Text != "".
observed(Doing) :- got(Doing, _, _).
met(Requirement) :- met_by(Requirement, Doing), observed(Doing).
accounted_for(Text) :- about(Text, Requirement), met(Requirement).
purpose(Law) :- law(Law).
purpose(Predicate) :- output(Predicate, _).
serves_a_purpose(Requirement) :- serves(Requirement, Purpose), purpose(Purpose).
has_a_requirement(Doing) :- met_by(_, Doing).

violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).
violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).
violation("every_requirement_serves_a_purpose", Requirement) :- about(_, Requirement), !serves_a_purpose(Requirement).
violation("every_requirement_serves_a_purpose", Doing) :- does(Doing), !has_a_requirement(Doing).

a_law_is_broken() :- violation(_, _).
answer("false") :- a_law_is_broken().
answer("true") :- !a_law_is_broken().

belongs_to("universe.mg", "universe.mg").
belongs_to(Path, "machine.mg") :- machine_program(Path).
belongs_to(Path, "the machinery") :- language(Path, Language), !readable(Language).
in_a_leg(Path) :- belongs_to(Path, Leg), leg(Leg).

violation("every_file_belongs_to_a_leg", Path) :- universe_file(Path), !in_a_leg(Path).

in_a_case() :- started_by("run_a_case").
case(Case) :- case_answer(Case, _).
running_a_case(Doing, Case) :- case(Case), !in_a_case(), Doing = fn:string:concat("run the case ", Case).
does(Doing) :- running_a_case(Doing, _).
effect(Doing, "run_a_case") :- running_a_case(Doing, _).
gives(Doing, Path, Line) :- running_a_case(Doing, Case), case_adds_line(Case, Path, Line).
broke_in(Case, Law) :- running_a_case(Doing, Case), got(Doing, "violation", Law).
answered(Case, Answer) :- running_a_case(Doing, Case), got(Doing, "exit", Code), exit_code(Answer, Code).
missed(Case) :- case_expects(Case, Law), !broke_in(Case, Law).
came_out_as_stated(Case) :- case_answer(Case, Answer), answered(Case, Answer), !missed(Case).
shown_failing(Law) :- case_expects(_, Law).

violation("every_law_is_shown_failing", Law) :- law(Law), !shown_failing(Law).
violation("every_case_comes_out_as_stated", Case) :- case(Case), !in_a_case(), !came_out_as_stated(Case), !case_differs(Case).
violation("every_case_comes_out_as_stated", Case) :- case_differs(Case), came_out_as_stated(Case).

case_adds_line("a file that is not datalog", "notes.txt", "a note").
case_expects("a file that is not datalog", "the_only_knowledge_is_datalog").
case_answer("a file that is not datalog", "false").

case_adds_line("a program that fakes an observation", "machine.mg", 'got("list the universe", "file", "nowhere").').
case_expects("a program that fakes an observation", "each_word_has_one_supplier").
case_answer("a program that fakes an observation", "false").

case_adds_line("a line nobody accounts for", "universe.mg", 'lonely("a").').
case_expects("a line nobody accounts for", "every_line_is_accounted_for").
case_answer("a line nobody accounts for", "false").

case_adds_line("a requirement with no purpose", "machine.mg", 'about("no such line", "a requirement with no purpose").').
case_expects("a requirement with no purpose", "every_requirement_serves_a_purpose").
case_answer("a requirement with no purpose", "false").

case_adds_line("a file outside the legs", "notes.mg", 'note("a").').
case_expects("a file outside the legs", "every_file_belongs_to_a_leg").
case_answer("a file outside the legs", "false").

case_adds_line("a law with no case", "machine.mg", 'violation("a_law_with_no_case", Path) :- universe_file(Path), :string:ends_with(Path, ".txt").').
case_expects("a law with no case", "every_law_is_shown_failing").
case_answer("a law with no case", "false").

case_adds_line("a world that cannot load", "universe.mg", "tells(").
case_answer("a world that cannot load", "broken").

case_expects("a case that differs", "every_case_comes_out_as_stated").
case_answer("a case that differs", "false").
case_differs("a case that differs").
