does("know the machine").
effect("know the machine", "know_the_machine").

violation("the_machine_is_the_one_asked_for", Want) :- mangle_module(Want), !got("know the machine", "mangle_module", Want).
violation("the_machine_is_the_one_asked_for", Want) :- mangle_version(Want), !got("know the machine", "mangle_version", Want).
violation("the_machine_is_the_one_asked_for", Want) :- entry_point(Want), got("know the machine", "entry_point", Got), Got != Want.

taken_out(Taking, Text) :- universe_line(Text), Taking = fn:string:concat("take out ", Text).
does(Taking) :- taken_out(Taking, _).
effect(Taking, "take_out_a_line") :- taken_out(Taking, _).
gives(Taking, "path", Path) :- taken_out(Taking, _), gives("read the universe", "path", Path).
gives(Taking, "line", Text) :- taken_out(Taking, Text).

met_by("the machine", "know the machine").
met_by("the listing", "list the universe").
met_by("the comments", Doing) :- finding_comments(Doing, _).
met_by("the reading", "read the universe").
met_by("the taking out", Taking) :- taken_out(Taking, _).
met_by("every doing", Doing) :- does(Doing).

about('mangle_module("codeberg.org/TauCeti/mangle-go").', "the machine").
about('mangle_version("v0.7.0").', "the machine").
about('entry_point("run.me").', "the machine").
about('machine_program("machine.mg").', "the machine").
about('code_ending(".go").', "the listing").
about('module_ending("go.mod").', "the listing").
about('module_ending("go.sum").', "the listing").
about('Decl got(Doing, Field, Value).', "every doing").
about('Decl about(Text, Requirement).', "the reading").
about('Decl met_by(Requirement, Doing).', "every doing").
about('Decl taken_out(Doing, Text).', "the taking out").
about('does("list the universe").', "the listing").
about('effect("list the universe", "list_a_folder").', "the listing").
about('gives("list the universe", "folder", ".").', "the listing").
about('universe_file(Path) :- got("list the universe", "file", Path).', "the listing").
about('tells(Path) :- universe_file(Path).', "the listing").
about('datalog(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").', "the listing").
about('code(Path) :- universe_file(Path), entry_point(Path).', "the listing").
about('code(Path) :- universe_file(Path), code_ending(Ending), :string:ends_with(Path, Ending).', "the listing").
about('machinery(Path) :- code(Path).', "the listing").
about('machinery(Path) :- universe_file(Path), module_ending(Ending), :string:ends_with(Path, Ending).', "the listing").
about('read_for_comments(Path) :- datalog(Path).', "the listing").
about('read_for_comments(Path) :- code(Path).', "the listing").
about('finding_comments(Doing, Path) :- read_for_comments(Path), Doing = fn:string:concat("find comments in ", Path).', "the comments").
about('does(Doing) :- finding_comments(Doing, _).', "the comments").
about('effect(Doing, "find_comments") :- finding_comments(Doing, _).', "the comments").
about('gives(Doing, "path", Path) :- finding_comments(Doing, Path).', "the comments").
about('violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !datalog(Path), !machinery(Path).', "the listing").
about('violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).', "the comments").
about('does("read the universe").', "the reading").
about('effect("read the universe", "read_lines").', "the reading").
about('gives("read the universe", "path", "universe.mg").', "the reading").
about('universe_line(Text) :- got("read the universe", "line", Text), Text != "".', "the reading").
about('observed(Doing) :- got(Doing, _, _).', "every doing").
about('met(Requirement) :- met_by(Requirement, Doing), observed(Doing).', "every doing").
about('accounted_for(Text) :- about(Text, Requirement), met(Requirement).', "the reading").
about('changes_its_step(Text) :- taken_out(Taking, Text), about(Text, Requirement), met_by(Requirement, Doing), got(Taking, "changed", Doing).', "the taking out").
about('violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).', "the listing").
about('violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).', "the reading").
about('violation("every_line_is_real", Text) :- universe_line(Text), !changes_its_step(Text).', "the reading").
