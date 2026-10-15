does("know the machine").
effect("know the machine", "know_the_machine").

violation("the_machine_is_the_one_asked_for", Want) :- mangle_module(Want), !got("know the machine", "mangle_module", Want).
violation("the_machine_is_the_one_asked_for", Want) :- mangle_version(Want), !got("know the machine", "mangle_version", Want).
violation("the_machine_is_the_one_asked_for", Want) :- entry_point(Want), got("know the machine", "entry_point", Got), Got != Want.

account(Text, "know the machine") :- line_about(Text, "the machine").
account(Text, "list the universe") :- line_about(Text, "the listing").
account(Text, Doing) :- line_about(Text, "the comments"), finding_comments(Doing, _).
account(Text, "read the universe") :- line_about(Text, "the reading").
account(Text, Doing) :- line_about(Text, "every doing"), does(Doing).

line_about('mangle_module("codeberg.org/TauCeti/mangle-go").', "the machine").
line_about('mangle_version("v0.7.0").', "the machine").
line_about('entry_point("run.me").', "the machine").
line_about('machine_program("machine.mg").', "the machine").
line_about('code_ending(".go").', "the listing").
line_about('module_ending("go.mod").', "the listing").
line_about('module_ending("go.sum").', "the listing").
line_about('', "the reading").
line_about('Decl got(Doing, Field, Value).', "every doing").
line_about('Decl account(Text, Doing).', "the reading").
line_about('does("list the universe").', "the listing").
line_about('effect("list the universe", "list_a_folder").', "the listing").
line_about('gives("list the universe", "folder", ".").', "the listing").
line_about('universe_file(Path) :- got("list the universe", "file", Path).', "the listing").
line_about('tells(Path) :- universe_file(Path).', "the listing").
line_about('datalog(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").', "the listing").
line_about('code(Path) :- universe_file(Path), entry_point(Path).', "the listing").
line_about('code(Path) :- universe_file(Path), code_ending(Ending), :string:ends_with(Path, Ending).', "the listing").
line_about('machinery(Path) :- code(Path).', "the listing").
line_about('machinery(Path) :- universe_file(Path), module_ending(Ending), :string:ends_with(Path, Ending).', "the listing").
line_about('read_for_comments(Path) :- datalog(Path).', "the listing").
line_about('read_for_comments(Path) :- code(Path).', "the listing").
line_about('finding_comments(Doing, Path) :- read_for_comments(Path), Doing = fn:string:concat("find comments in ", Path).', "the comments").
line_about('does(Doing) :- finding_comments(Doing, _).', "the comments").
line_about('effect(Doing, "find_comments") :- finding_comments(Doing, _).', "the comments").
line_about('gives(Doing, "path", Path) :- finding_comments(Doing, Path).', "the comments").
line_about('violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !datalog(Path), !machinery(Path).', "the listing").
line_about('violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).', "the comments").
line_about('does("read the universe").', "the reading").
line_about('effect("read the universe", "read_lines").', "the reading").
line_about('gives("read the universe", "path", "universe.mg").', "the reading").
line_about('universe_line(Text) :- got("read the universe", "line", Text).', "the reading").
line_about('observed(Doing) :- got(Doing, _, _).', "every doing").
line_about('accounted_for(Text) :- account(Text, Doing), observed(Doing).', "the reading").
line_about('violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).', "the listing").
line_about('violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).', "the reading").
