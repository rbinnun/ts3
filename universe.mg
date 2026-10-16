mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
machine_program("machine.mg").
code_ending(".go").
module_ending("go.mod").
module_ending("go.sum").

Decl got(Doing, Field, Value).
Decl about(Text, Requirement).
Decl met_by(Requirement, Doing).

why("universe.mg", "it is a general spec: it says what must be true, not how").
why("machine.mg", "it makes the spec specific: for every line of universe.mg it shows the path from that line to what the world does, so that universe.mg and machine.mg together are enough for someone else to build the machinery again").
why("the declarations", "the words the machine supplies are declared, so a misspelled name stops the run instead of quietly matching nothing").
why("the_only_knowledge_is_datalog", "knowledge kept in code, comments or prose is hidden from the world: nothing can read it, check it or prove it").
why("the machinery", "every line of code is knowledge the world cannot read, so the machinery holds only what the spec needs").
why("every_line_is_accounted_for", "a line with no path to what the world does is knowledge nobody uses").

does("list the universe").
effect("list the universe", "list_a_folder").
gives("list the universe", "folder", ".").

universe_file(Path) :- got("list the universe", "file", Path).
tells(Path) :- universe_file(Path).

datalog(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").
code(Path) :- universe_file(Path), entry_point(Path).
code(Path) :- universe_file(Path), code_ending(Ending), :string:ends_with(Path, Ending).
machinery(Path) :- code(Path).
machinery(Path) :- universe_file(Path), module_ending(Ending), :string:ends_with(Path, Ending).

read_for_comments(Path) :- datalog(Path).
read_for_comments(Path) :- code(Path).

finding_comments(Doing, Path) :- read_for_comments(Path), Doing = fn:string:concat("find comments in ", Path).
does(Doing) :- finding_comments(Doing, _).
effect(Doing, "find_comments") :- finding_comments(Doing, _).
gives(Doing, "path", Path) :- finding_comments(Doing, Path).

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !datalog(Path), !machinery(Path).
violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).

does("read the universe").
effect("read the universe", "read_lines").
gives("read the universe", "path", "universe.mg").

universe_line(Text) :- got("read the universe", "line", Text), Text != "".
observed(Doing) :- got(Doing, _, _).
met(Requirement) :- met_by(Requirement, Doing), observed(Doing).
accounted_for(Text) :- about(Text, Requirement), met(Requirement).

violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).
violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).
