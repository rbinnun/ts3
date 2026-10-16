mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
machine_program("machine.mg").

leg("universe.mg").
leg("machine.mg").
leg("the machinery").
rebuilt_from(Leg, Other) :- leg(Leg), leg(Other), Leg != Other.
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

output("tells", "mangle").
output("violation", "mangle").

exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

Decl got(Doing, Field, Value).
Decl about(Text, Requirement).
Decl met_by(Requirement, Doing).
Decl serves(Requirement, Purpose).

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

violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).
violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).
violation("every_requirement_serves_a_purpose", Requirement) :- about(_, Requirement), !serves_a_purpose(Requirement).

a_law_is_broken() :- violation(_, _).
answer("false") :- a_law_is_broken().
answer("true") :- !a_law_is_broken().
