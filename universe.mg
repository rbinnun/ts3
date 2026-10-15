mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
code_ending(".go").
module_ending("go.mod").
module_ending("go.sum").

Decl got(Doing, Field, Value).

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
