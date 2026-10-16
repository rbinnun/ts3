does("know the machine").
effect("know the machine", "know_the_machine").

violation("the_machine_is_the_one_asked_for", Want) :- mangle_module(Want), !got("know the machine", "mangle_module", Want).
violation("the_machine_is_the_one_asked_for", Want) :- mangle_version(Want), !got("know the machine", "mangle_version", Want).
violation("the_machine_is_the_one_asked_for", Want) :- entry_point(Want), !got("know the machine", "entry_point", Want).
violation("the_machine_is_the_one_asked_for", Path) :- machine_program(Path), !got("know the machine", "machine_program", Path).
violation("the_machine_is_the_one_asked_for", "broken") :- exit_code("broken", Code), !got("know the machine", "exits_broken_with", Code).

case_adds_line("a machine that is not the one asked for", "machine.mg", 'mangle_version("v0.0.0").').
case_expects("a machine that is not the one asked for", "the_machine_is_the_one_asked_for").
case_answer("a machine that is not the one asked for", "false").

gives(Doing, "laws_in", "violation") :- reading_a_program(Doing, _).

met_by("universe.mg", "read the universe").
met_by("machine.mg", "know the machine").
met_by("machine.mg", Doing) :- reading_a_program(Doing, Path), machine_program(Path).
met_by("the machinery", "know the machine").
met_by("the machinery", Doing) :- finding_comments(Doing, Path), !datalog(Path).
met_by("this folder", "list the universe").
met_by("the legs", "list the universe").
met_by("the declarations", "know the machine").
met_by("the declarations", Doing) :- reading_a_program(Doing, Path), machine_program(Path).
met_by("the languages", "list the universe").
met_by("the languages", Doing) :- finding_comments(Doing, _).
met_by("the programs", Doing) :- reading_a_program(Doing, _).
met_by("the suppliers", Doing) :- reading_a_program(Doing, _).
met_by("the lines", "read the universe").
met_by("the purposes", Doing) :- reading_a_program(Doing, _).
met_by("the requirements", Doing) :- reading_a_program(Doing, _).
met_by("the leg of each file", "list the universe").
met_by("the cases", Doing) :- running_a_case(Doing, _).
met_by("the cases", "know the machine") :- got("know the machine", "started_by", "run_a_case").
met_by("the outcomes", Doing) :- running_a_case(Doing, _).
met_by("the outcomes", "know the machine") :- got("know the machine", "started_by", "run_a_case").
met_by("the laws", Doing) :- reading_a_program(Doing, _).
met_by("the clauses", Doing) :- reading_a_program(Doing, _).
met_by("the answer", "know the machine").

serves("universe.mg", "every_line_is_accounted_for").
serves("machine.mg", "every_line_is_accounted_for").
serves("the machinery", "the_machine_is_the_one_asked_for").
serves("this folder", "tells").
serves("the legs", "every_file_belongs_to_a_leg").
serves("the declarations", "each_word_has_one_supplier").
serves("the languages", "the_only_knowledge_is_datalog").
serves("the programs", "each_word_has_one_supplier").
serves("the programs", "every_requirement_serves_a_purpose").
serves("the suppliers", "each_word_has_one_supplier").
serves("the lines", "every_line_is_accounted_for").
serves("the purposes", "every_requirement_serves_a_purpose").
serves("the requirements", "every_requirement_is_specific").
serves("the leg of each file", "every_file_belongs_to_a_leg").
serves("the cases", "every_case_comes_out_as_stated").
serves("the cases", "every_law_is_shown_failing").
serves("the outcomes", "every_case_comes_out_as_stated").
serves("the laws", "every_law_is_shown_failing").
serves("the clauses", "unfired").
serves("the answer", "violation").
serves("the answer", "the_machine_is_the_one_asked_for").

about('mangle_module("codeberg.org/TauCeti/mangle-go").', "the machinery").
about('mangle_version("v0.7.0").', "the machinery").
about('entry_point("run.me").', "the machinery").
about('machine_program("machine.mg").', "machine.mg").
about('leg("universe.mg").', "universe.mg").
about('leg("machine.mg").', "machine.mg").
about('leg("the machinery").', "the machinery").
about('rebuilt_from(Leg, Other) :- leg(Leg), leg(Other), Leg != Other.', "the legs").
about('source_of_truth("universe.mg").', "the legs").
about('a_rebuild_replaces(Leg) :- leg(Leg), !source_of_truth(Leg).', "the legs").
about('a_rebuild_proposes(Leg) :- source_of_truth(Leg).', "the legs").
about('written_by("universe.mg", "the owner").', "universe.mg").
about('written_by("machine.mg", "the builder").', "machine.mg").
about('written_by("the machinery", "the builder").', "the machinery").
about('written_in(".mg", "mangle").', "the languages").
about('written_in(".go", "go").', "the languages").
about('written_in("go.mod", "go module").', "the languages").
about('written_in("go.sum", "go checksums").', "the languages").
about('written_in(Entry, "sh") :- entry_point(Entry).', "the languages").
about('readable("mangle").', "the programs").
about('has_comments("mangle").', "the languages").
about('has_comments("go").', "the languages").
about('has_comments("sh").', "the languages").
about('supplied_by("got", "the machine").', "the suppliers").
about('supplied_by("about", "machine.mg").', "the suppliers").
about('supplied_by("met_by", "machine.mg").', "the suppliers").
about('supplied_by("serves", "machine.mg").', "the suppliers").
about('supplied_by("started_by", "the machine").', "the suppliers").
about('supplied_by("fired", "the machine").', "the suppliers").
about('supplied_by("fired_in_a_case", "the machine").', "the suppliers").
about('output("tells", "mangle").', "this folder").
about('output("answer", "mangle").', "the answer").
about('output("violation", "mangle").', "the answer").
about('output("case_broke", "mangle").', "the outcomes").
about('output("case_answered", "mangle").', "the outcomes").
about('output("unfired", "mangle").', "the clauses").
about('exit_code("true", 0).', "the answer").
about('exit_code("false", 1).', "the answer").
about('exit_code("broken", 2).', "the answer").
about('Decl got(Doing, Field, Value).', "the declarations").
about('Decl about(Text, Requirement).', "the declarations").
about('Decl met_by(Requirement, Doing).', "the declarations").
about('Decl serves(Requirement, Purpose).', "the declarations").
about('Decl started_by(Effect).', "the declarations").
about('Decl fired(Path, Line).', "the declarations").
about('Decl fired_in_a_case(Path, Line).', "the declarations").
about('does("list the universe").', "this folder").
about('effect("list the universe", "list_a_folder").', "this folder").
about('gives("list the universe", "folder", ".").', "this folder").
about('universe_file(Path) :- got("list the universe", "file", Path).', "this folder").
about('tells(Path) :- universe_file(Path).', "this folder").
about('language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).', "the languages").
about('known(Path) :- language(Path, _).', "the languages").
about('datalog(Path) :- language(Path, Language), readable(Language).', "the programs").
about('finding_comments(Doing, Path) :- language(Path, Language), has_comments(Language), Doing = fn:string:concat("find comments in ", Path).', "the languages").
about('does(Doing) :- finding_comments(Doing, _).', "the languages").
about('effect(Doing, "find_comments") :- finding_comments(Doing, _).', "the languages").
about('gives(Doing, "path", Path) :- finding_comments(Doing, Path).', "the languages").
about('gives(Doing, "language", Language) :- finding_comments(Doing, Path), language(Path, Language).', "the languages").
about('reading_a_program(Doing, Path) :- datalog(Path), Doing = fn:string:concat("read the program ", Path).', "the programs").
about('does(Doing) :- reading_a_program(Doing, _).', "the programs").
about('effect(Doing, "read_a_program") :- reading_a_program(Doing, _).', "the programs").
about('gives(Doing, "path", Path) :- reading_a_program(Doing, Path).', "the programs").
about('defines(Path, Predicate) :- reading_a_program(Doing, Path), got(Doing, "defines", Predicate).', "the suppliers").
about('law(Law) :- reading_a_program(Doing, _), got(Doing, "law", Law).', "the purposes").
about('clause_line(Path, Line) :- reading_a_program(Doing, Path), got(Doing, "clause", Line).', "the clauses").
about('unfired(Path, Line) :- clause_line(Path, Line), !fired(Path, Line), !fired_in_a_case(Path, Line).', "the clauses").
about('violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).', "the languages").
about('violation("the_only_knowledge_is_datalog", Path) :- finding_comments(Doing, Path), got(Doing, "comment", _).', "the languages").
about('violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.', "the suppliers").
about('does("read the universe").', "universe.mg").
about('effect("read the universe", "read_lines").', "universe.mg").
about('gives("read the universe", "path", "universe.mg").', "universe.mg").
about('universe_line(Text) :- got("read the universe", "line", Text), Text != "".', "the lines").
about('observed(Doing) :- got(Doing, _, _).', "the lines").
about('met(Requirement) :- met_by(Requirement, Doing), observed(Doing).', "the lines").
about('accounted_for(Text) :- about(Text, Requirement), met(Requirement).', "the lines").
about('purpose(Law) :- law(Law).', "the purposes").
about('purpose(Predicate) :- output(Predicate, _).', "the purposes").
about('serves_a_purpose(Requirement) :- serves(Requirement, Purpose), purpose(Purpose).', "the purposes").
about('has_a_requirement(Doing) :- met_by(_, Doing).', "the purposes").
about('violation("every_line_is_accounted_for", Path) :- machine_program(Path), !universe_file(Path).', "machine.mg").
about('violation("every_line_is_accounted_for", Text) :- universe_line(Text), !accounted_for(Text).', "the lines").
about('violation("every_requirement_serves_a_purpose", Requirement) :- about(_, Requirement), !serves_a_purpose(Requirement).', "the purposes").
about('violation("every_requirement_serves_a_purpose", Doing) :- does(Doing), !has_a_requirement(Doing).', "the purposes").
about('requirement(Requirement) :- met_by(Requirement, _).', "the requirements").
about('misses_a_step(Requirement) :- requirement(Requirement), does(Doing), !met_by(Requirement, Doing).', "the requirements").
about('violation("every_requirement_is_specific", Requirement) :- serves(Requirement, Requirement).', "the requirements").
about('violation("every_requirement_is_specific", Requirement) :- requirement(Requirement), !misses_a_step(Requirement).', "the requirements").
about('a_law_is_broken() :- violation(_, _).', "the answer").
about('answer("false") :- a_law_is_broken().', "the answer").
about('answer("true") :- !a_law_is_broken().', "the answer").
about('belongs_to("universe.mg", "universe.mg").', "the leg of each file").
about('belongs_to(Path, "machine.mg") :- machine_program(Path).', "the leg of each file").
about('belongs_to(Path, "the machinery") :- language(Path, Language), !readable(Language).', "the leg of each file").
about('in_a_leg(Path) :- belongs_to(Path, Leg), leg(Leg).', "the leg of each file").
about('violation("every_file_belongs_to_a_leg", Path) :- universe_file(Path), !in_a_leg(Path).', "the leg of each file").
about('in_a_case() :- started_by("run_a_case").', "the cases").
about('case(Case) :- case_answer(Case, _).', "the cases").
about('running_a_case(Doing, Case) :- case(Case), !in_a_case(), Doing = fn:string:concat("run the case ", Case).', "the cases").
about('does(Doing) :- running_a_case(Doing, _).', "the cases").
about('effect(Doing, "run_a_case") :- running_a_case(Doing, _).', "the cases").
about('gives(Doing, Path, Line) :- running_a_case(Doing, Case), case_adds_line(Case, Path, Line).', "the cases").
about('case_broke(Case, Law) :- running_a_case(Doing, Case), got(Doing, "violation", Law).', "the outcomes").
about('case_answered(Case, Answer) :- running_a_case(Doing, Case), got(Doing, "exit", Code), exit_code(Answer, Code).', "the outcomes").
about('missed(Case) :- case_expects(Case, Law), !case_broke(Case, Law).', "the outcomes").
about('came_out_as_stated(Case) :- case_answer(Case, Answer), case_answered(Case, Answer), !missed(Case).', "the outcomes").
about('off_from_stated(Case) :- case(Case), !in_a_case(), !came_out_as_stated(Case).', "the outcomes").
about('expects_no_law(Case) :- case_expects(Case, Law), !law(Law).', "the outcomes").
about('shown_failing(Law) :- case_broke(_, Law).', "the laws").
about('shown_failing(Law) :- in_a_case(), case_expects(_, Law).', "the laws").
about('violation("every_law_is_shown_failing", Law) :- law(Law), !shown_failing(Law).', "the laws").
about('violation("every_case_comes_out_as_stated", Case) :- off_from_stated(Case).', "the outcomes").
about('violation("every_case_comes_out_as_stated", Case) :- expects_no_law(Case).', "the outcomes").
about('case_adds_line("a file that is not datalog", "notes.txt", "a note").', "the cases").
about('case_expects("a file that is not datalog", "the_only_knowledge_is_datalog").', "the cases").
about('case_answer("a file that is not datalog", "false").', "the cases").
about('case_adds_line("a program that fakes an observation", "machine.mg", \'got("list the universe", "file", "nowhere").\').', "the cases").
about('case_expects("a program that fakes an observation", "each_word_has_one_supplier").', "the cases").
about('case_answer("a program that fakes an observation", "false").', "the cases").
about('case_adds_line("a line nobody accounts for", "universe.mg", \'lonely("a").\').', "the cases").
about('case_expects("a line nobody accounts for", "every_line_is_accounted_for").', "the cases").
about('case_answer("a line nobody accounts for", "false").', "the cases").
about('case_adds_line("a requirement with no purpose", "machine.mg", \'about("no such line", "a requirement with no purpose").\').', "the cases").
about('case_expects("a requirement with no purpose", "every_requirement_serves_a_purpose").', "the cases").
about('case_answer("a requirement with no purpose", "false").', "the cases").
about('case_adds_line("a file outside the legs", "notes.mg", \'note("a").\').', "the cases").
about('case_expects("a file outside the legs", "every_file_belongs_to_a_leg").', "the cases").
about('case_answer("a file outside the legs", "false").', "the cases").
about('case_adds_line("a law with no case", "machine.mg", \'violation("a_law_with_no_case", Path) :- universe_file(Path), :string:ends_with(Path, ".txt").\').', "the cases").
about('case_expects("a law with no case", "every_law_is_shown_failing").', "the cases").
about('case_answer("a law with no case", "false").', "the cases").
about('case_adds_line("a world that cannot load", "universe.mg", "tells(").', "the cases").
about('case_answer("a world that cannot load", "broken").', "the cases").
about('case_adds_line("a case that expects a law nobody laid down", "machine.mg", \'case_expects("a ghost case", "a_law_nobody_laid_down").\').', "the cases").
about('case_expects("a case that expects a law nobody laid down", "every_case_comes_out_as_stated").', "the cases").
about('case_answer("a case that expects a law nobody laid down", "false").', "the cases").
about('case_adds_line("a requirement that serves itself", "machine.mg", \'serves("a self-serving requirement", "a self-serving requirement").\').', "the cases").
about('case_expects("a requirement that serves itself", "every_requirement_is_specific").', "the cases").
about('case_answer("a requirement that serves itself", "false").', "the cases").
about('case_adds_line("a requirement met by every step", "machine.mg", \'met_by("a requirement met by every step", Doing) :- does(Doing).\').', "the cases").
about('case_expects("a requirement met by every step", "every_requirement_is_specific").', "the cases").
about('case_answer("a requirement met by every step", "false").', "the cases").
about('case_adds_line("a comment", "machine.mg", "# a note").', "the cases").
about('case_expects("a comment", "the_only_knowledge_is_datalog").', "the cases").
about('case_answer("a comment", "false").', "the cases").
about('case_adds_line("a step with no requirement", "machine.mg", \'does("an idle step").\').', "the cases").
about('case_adds_line("a step with no requirement", "machine.mg", \'effect("an idle step", "list_a_folder").\').', "the cases").
about('case_adds_line("a step with no requirement", "machine.mg", \'gives("an idle step", "folder", ".").\').', "the cases").
about('case_expects("a step with no requirement", "every_requirement_serves_a_purpose").', "the cases").
about('case_answer("a step with no requirement", "false").', "the cases").
about('case_adds_line("a machine program that is missing", "universe.mg", \'machine_program("missing.mg").\').', "the cases").
about('case_expects("a machine program that is missing", "every_line_is_accounted_for").', "the cases").
about('case_answer("a machine program that is missing", "false").', "the cases").
