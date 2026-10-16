does("know the machine").
effect("know the machine", "know_the_machine").

violation("the_machine_is_the_one_asked_for", Want) :- mangle_module(Want), !got("know the machine", "mangle_module", Want).
violation("the_machine_is_the_one_asked_for", Want) :- mangle_version(Want), !got("know the machine", "mangle_version", Want).
violation("the_machine_is_the_one_asked_for", Want) :- entry_point(Want), !got("know the machine", "entry_point", Want).
violation("the_machine_is_the_one_asked_for", Path) :- machine_program(Path), !got("know the machine", "machine_program", Path).
violation("the_machine_is_the_one_asked_for", "broken") :- exit_code("broken", Code), !got("know the machine", "exits_broken_with", Code).

gives(Doing, "laws_in", "violation") :- reading_a_program(Doing, _).

met_by("universe.mg", "read the universe").
met_by("machine.mg", "know the machine").
met_by("machine.mg", Doing) :- reading_a_program(Doing, Path), machine_program(Path).
met_by("the machinery", "know the machine").
met_by("the machinery", Doing) :- finding_comments(Doing, Path), !datalog(Path).
met_by("this folder", "list the universe").
met_by("the declarations", Doing) :- does(Doing).
met_by("the_only_knowledge_is_datalog", "list the universe").
met_by("the_only_knowledge_is_datalog", Doing) :- finding_comments(Doing, _).
met_by("the programs", Doing) :- reading_a_program(Doing, _).
met_by("each_word_has_one_supplier", Doing) :- reading_a_program(Doing, _).
met_by("every_line_is_accounted_for", "read the universe").
met_by("every_requirement_serves_a_purpose", Doing) :- reading_a_program(Doing, _).
met_by("the answer", "know the machine").

serves("universe.mg", "every_line_is_accounted_for").
serves("machine.mg", "every_line_is_accounted_for").
serves("the machinery", "the_machine_is_the_one_asked_for").
serves("this folder", "tells").
serves("the declarations", "each_word_has_one_supplier").
serves("the_only_knowledge_is_datalog", "the_only_knowledge_is_datalog").
serves("the programs", "each_word_has_one_supplier").
serves("the programs", "every_requirement_serves_a_purpose").
serves("each_word_has_one_supplier", "each_word_has_one_supplier").
serves("every_line_is_accounted_for", "every_line_is_accounted_for").
serves("every_requirement_serves_a_purpose", "every_requirement_serves_a_purpose").
serves("the answer", "violation").
serves("the answer", "the_machine_is_the_one_asked_for").

about('mangle_module("codeberg.org/TauCeti/mangle-go").', "the machinery").
about('mangle_version("v0.7.0").', "the machinery").
about('entry_point("run.me").', "the machinery").
about('machine_program("machine.mg").', "machine.mg").
about('leg("universe.mg").', "universe.mg").
about('leg("machine.mg").', "machine.mg").
about('leg("the machinery").', "the machinery").
about('rebuilt_from(Leg, Other) :- leg(Leg), leg(Other), Leg != Other.', "every_line_is_accounted_for").
about('written_by("universe.mg", "the owner").', "universe.mg").
about('written_by("machine.mg", "the builder").', "machine.mg").
about('written_by("the machinery", "the builder").', "the machinery").
about('written_in(".mg", "mangle").', "the_only_knowledge_is_datalog").
about('written_in(".go", "go").', "the_only_knowledge_is_datalog").
about('written_in("go.mod", "go module").', "the_only_knowledge_is_datalog").
about('written_in("go.sum", "go checksums").', "the_only_knowledge_is_datalog").
about('written_in(Entry, "sh") :- entry_point(Entry).', "the_only_knowledge_is_datalog").
about('readable("mangle").', "the programs").
about('has_comments("mangle").', "the_only_knowledge_is_datalog").
about('has_comments("go").', "the_only_knowledge_is_datalog").
about('has_comments("sh").', "the_only_knowledge_is_datalog").
about('supplied_by("got", "the machine").', "each_word_has_one_supplier").
about('supplied_by("about", "machine.mg").', "each_word_has_one_supplier").
about('supplied_by("met_by", "machine.mg").', "each_word_has_one_supplier").
about('supplied_by("serves", "machine.mg").', "each_word_has_one_supplier").
about('output("tells", "mangle").', "this folder").
about('output("violation", "mangle").', "the answer").
about('exit_code("true", 0).', "the answer").
about('exit_code("false", 1).', "the answer").
about('exit_code("broken", 2).', "the answer").
about('Decl got(Doing, Field, Value).', "the declarations").
about('Decl about(Text, Requirement).', "the declarations").
about('Decl met_by(Requirement, Doing).', "the declarations").
about('Decl serves(Requirement, Purpose).', "the declarations").
about('does("list the universe").', "this folder").
about('effect("list the universe", "list_a_folder").', "this folder").
about('gives("list the universe", "folder", ".").', "this folder").
about('universe_file(Path) :- got("list the universe", "file", Path).', "this folder").
about('tells(Path) :- universe_file(Path).', "this folder").
about('language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).', "the_only_knowledge_is_datalog").
about('known(Path) :- language(Path, _).', "the_only_knowledge_is_datalog").
about('datalog(Path) :- language(Path, Language), readable(Language).', "the programs").
about('finding_comments(Doing, Path) :- language(Path, Language), has_comments(Language), Doing = fn:string:concat("find comments in ", Path).', "the_only_knowledge_is_datalog").
about('does(Doing) :- finding_comments(Doing, _).', "the_only_knowledge_is_datalog").
about('effect(Doing, "find_comments") :- finding_comments(Doing, _).', "the_only_knowledge_is_datalog").
about('gives(Doing, "path", Path) :- finding_comments(Doing, Path).', "the_only_knowledge_is_datalog").
about('gives(Doing, "language", Language) :- finding_comments(Doing, Path), language(Path, Language).', "the_only_knowledge_is_datalog").
about('reading_a_program(Doing, Path) :- datalog(Path), Doing = fn:string:concat("read the program ", Path).', "the programs").
about('does(Doing) :- reading_a_program(Doing, _).', "the programs").
about('effect(Doing, "read_a_program") :- reading_a_program(Doing, _).', "the programs").
about('gives(Doing, "path", Path) :- reading_a_program(Doing, Path).', "the programs").
about('defines(Path, Predicate) :- reading_a_program(Doing, Path), got(Doing, "defines", Predicate).', "each_word_has_one_supplier").
about('law(Law) :- reading_a_program(Doing, _), got(Doing, "law", Law).', "every_requirement_serves_a_purpose").
about('violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).', "the_only_knowledge_is_datalog").
about('violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).', "the_only_knowledge_is_datalog").
about('violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.', "each_word_has_one_supplier").
about('does("read the universe").', "universe.mg").
about('effect("read the universe", "read_lines").', "universe.mg").
about('gives("read the universe", "path", "universe.mg").', "universe.mg").
about('universe_line(Text) :- got("read the universe", "line", Text), Text != "".', "every_line_is_accounted_for").
about('observed(Doing) :- got(Doing, _, _).', "every_line_is_accounted_for").
about('met(Requirement) :- met_by(Requirement, Doing), observed(Doing).', "every_line_is_accounted_for").
about('accounted_for(Text) :- about(Text, Requirement), met(Requirement).', "every_line_is_accounted_for").
about('purpose(Law) :- law(Law).', "every_requirement_serves_a_purpose").
about('purpose(Predicate) :- output(Predicate, _).', "every_requirement_serves_a_purpose").
about('serves_a_purpose(Requirement) :- serves(Requirement, Purpose), purpose(Purpose).', "every_requirement_serves_a_purpose").
about('violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).', "machine.mg").
about('violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).', "every_line_is_accounted_for").
about('violation("every_requirement_serves_a_purpose", Requirement) :- about(_, Requirement), !serves_a_purpose(Requirement).', "every_requirement_serves_a_purpose").
about('a_law_is_broken() :- violation(_, _).', "the answer").
about('answer("false") :- a_law_is_broken().', "the answer").
about('answer("true") :- !a_law_is_broken().', "the answer").
