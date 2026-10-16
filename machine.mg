does("know the machine").
effect("know the machine", "know_the_machine").

why("the_machine_is_the_one_asked_for", "the spec names the Mangle module, its version and the entry point it is run through, so a run on any other machine says nothing about whether the spec holds").

violation("the_machine_is_the_one_asked_for", Want) :- mangle_module(Want), !got("know the machine", "mangle_module", Want).
violation("the_machine_is_the_one_asked_for", Want) :- mangle_version(Want), !got("know the machine", "mangle_version", Want).
violation("the_machine_is_the_one_asked_for", Want) :- entry_point(Want), got("know the machine", "entry_point", Got), Got != Want.

met_by("universe.mg", "read the universe").
met_by("machine.mg", "know the machine").
met_by("this folder", "list the universe").
met_by("the declarations", Doing) :- does(Doing).
met_by("the_only_knowledge_is_datalog", "list the universe").
met_by("the_only_knowledge_is_datalog", Doing) :- finding_comments(Doing, _).
met_by("the machinery", "know the machine").
met_by("the machinery", Doing) :- finding_comments(Doing, Path), code(Path).
met_by("every_line_is_accounted_for", "read the universe").
met_by("every_requirement_has_a_reason", "know the machine").

about('mangle_module("codeberg.org/TauCeti/mangle-go").', "the machinery").
about('mangle_version("v0.7.0").', "the machinery").
about('entry_point("run.me").', "the machinery").
about('machine_program("machine.mg").', "machine.mg").
about('code_ending(".go").', "the machinery").
about('module_ending("go.mod").', "the machinery").
about('module_ending("go.sum").', "the machinery").
about('Decl got(Doing, Field, Value).', "the declarations").
about('Decl about(Text, Requirement).', "the declarations").
about('Decl met_by(Requirement, Doing).', "the declarations").
about('why("universe.mg", "it is the general spec, written by its owner: it says what must be true, not how, and whoever builds the machine changes everything but this file").', "every_requirement_has_a_reason").
about('why("machine.mg", "it is the builder\'s reasoning in Datalog: it makes the spec specific, showing for every line of universe.mg the path from that line to what the world does, so that universe.mg and machine.mg together are enough for someone else to build the machinery again").', "every_requirement_has_a_reason").
about('why("this folder", "the universe is this folder and nothing outside it").', "every_requirement_has_a_reason").
about('why("the declarations", "the words the machine supplies are declared, so a misspelled name stops the run instead of quietly matching nothing").', "every_requirement_has_a_reason").
about('why("the_only_knowledge_is_datalog", "knowledge kept in code, comments or prose is hidden from the world: nothing can read it, check it or prove it").', "every_requirement_has_a_reason").
about('why("the machinery", "every line of code is knowledge the world cannot read, so the machinery holds only what the spec needs").', "every_requirement_has_a_reason").
about('why("every_line_is_accounted_for", "a line with no path to what the world does is knowledge nobody uses; the account is a justification for the owner to read and judge, not a proof").', "every_requirement_has_a_reason").
about('why("every_requirement_has_a_reason", "a requirement without a reason cannot be judged: its why says what it means and why it is there").', "every_requirement_has_a_reason").
about('does("list the universe").', "this folder").
about('effect("list the universe", "list_a_folder").', "this folder").
about('gives("list the universe", "folder", ".").', "this folder").
about('universe_file(Path) :- got("list the universe", "file", Path).', "this folder").
about('tells(Path) :- universe_file(Path).', "this folder").
about('datalog(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").', "the_only_knowledge_is_datalog").
about('code(Path) :- universe_file(Path), entry_point(Path).', "the machinery").
about('code(Path) :- universe_file(Path), code_ending(Ending), :string:ends_with(Path, Ending).', "the machinery").
about('machinery(Path) :- code(Path).', "the machinery").
about('machinery(Path) :- universe_file(Path), module_ending(Ending), :string:ends_with(Path, Ending).', "the machinery").
about('read_for_comments(Path) :- datalog(Path).', "the_only_knowledge_is_datalog").
about('read_for_comments(Path) :- code(Path).', "the_only_knowledge_is_datalog").
about('finding_comments(Doing, Path) :- read_for_comments(Path), Doing = fn:string:concat("find comments in ", Path).', "the_only_knowledge_is_datalog").
about('does(Doing) :- finding_comments(Doing, _).', "the_only_knowledge_is_datalog").
about('effect(Doing, "find_comments") :- finding_comments(Doing, _).', "the_only_knowledge_is_datalog").
about('gives(Doing, "path", Path) :- finding_comments(Doing, Path).', "the_only_knowledge_is_datalog").
about('violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !datalog(Path), !machinery(Path).', "the_only_knowledge_is_datalog").
about('violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).', "the_only_knowledge_is_datalog").
about('does("read the universe").', "universe.mg").
about('effect("read the universe", "read_lines").', "universe.mg").
about('gives("read the universe", "path", "universe.mg").', "universe.mg").
about('universe_line(Text) :- got("read the universe", "line", Text), Text != "".', "every_line_is_accounted_for").
about('observed(Doing) :- got(Doing, _, _).', "every_line_is_accounted_for").
about('met(Requirement) :- met_by(Requirement, Doing), observed(Doing).', "every_line_is_accounted_for").
about('accounted_for(Text) :- about(Text, Requirement), met(Requirement).', "every_line_is_accounted_for").
about('violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).', "machine.mg").
about('violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).', "every_line_is_accounted_for").
about('reasoned(Requirement) :- why(Requirement, _).', "every_requirement_has_a_reason").
about('violation("every_requirement_has_a_reason", Requirement) :- about(_, Requirement), !reasoned(Requirement).', "every_requirement_has_a_reason").
