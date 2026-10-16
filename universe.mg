root("the world").
part_of("the legs", "the world").
part_of("the machine it runs on", "the legs").
part_of("who supplies what", "the world").
part_of("the only knowledge is Datalog", "the world").
part_of("file types", "the only knowledge is Datalog").
part_of("comments", "the only knowledge is Datalog").
part_of("the answer", "the world").
part_of("cases", "the world").
part_of("understanding", "the world").

in_branch("mangle_module", "the machine it runs on").
in_branch("mangle_version", "the machine it runs on").
in_branch("entry_point", "the machine it runs on").
in_branch("read_by_the_machinery", "the machine it runs on").
reads_as("mangle_module", "the world runs on the Mangle module {1}").
reads_as("mangle_version", "the Mangle version is {1}").
reads_as("entry_point", "the world is started with {1}").
reads_as("read_by_the_machinery", "the machinery reads the word {1}").

mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").
read_by_the_machinery("does").
read_by_the_machinery("effect").
read_by_the_machinery("gives").
read_by_the_machinery("machine_program").
read_by_the_machinery("output").
read_by_the_machinery("printed_in").
read_by_the_machinery("reads_as").
read_by_the_machinery("answer").
read_by_the_machinery("exit_code").

in_branch("machine_program", "the legs").
in_branch("leg", "the legs").
in_branch("source_of_truth", "the legs").
in_branch("written_by", "the legs").
in_branch("belongs_to", "the legs").
in_branch("in_a_leg", "the legs").
reads_as("machine_program", "{1} is a machine program").
reads_as("leg", "{1} is a leg").
reads_as("source_of_truth", "{1} is the source of truth").
reads_as("written_by", "{1} is written by {2}").
reads_as("belongs_to", "{1} belongs to the leg {2}").
reads_as("in_a_leg", "{1} is in a leg").

machine_program("machine.mg").
leg("universe.mg").
leg("machine.mg").
leg("the machinery").
source_of_truth("universe.mg").
written_by("universe.mg", "the owner").
written_by("machine.mg", "the builder").
written_by("the machinery", "the builder").

belongs_to("universe.mg", "universe.mg").
belongs_to(Path, "machine.mg") :- machine_program(Path).
belongs_to(Path, "the machinery") :- language(Path, Language), !readable(Language).
in_a_leg(Path) :- belongs_to(Path, Leg), leg(Leg).

violation("every_file_belongs_to_a_leg", Path) :- universe_file(Path), !in_a_leg(Path).
violation("the_world_sees_itself", "universe.mg") :- !universe_file("universe.mg").
violation("the_world_sees_itself", Path) :- machine_program(Path), !universe_file(Path).

case_adds_line("a file outside the legs", "notes.mg", 'note("a").').
case_expects("a file outside the legs", "every_file_belongs_to_a_leg").
case_answer("a file outside the legs", "false").

case_adds_line("a machine program that is missing", "universe.mg", 'machine_program("missing.mg").').
case_expects("a machine program that is missing", "the_world_sees_itself").
case_answer("a machine program that is missing", "false").

in_branch("supplied_by", "who supplies what").
in_branch("got", "who supplies what").
in_branch("started_by", "who supplies what").
in_branch("defines", "who supplies what").
reads_as("supplied_by", "the word {1} is supplied by {2}").
reads_as("got", "the step {1} got the {2} {3}").
reads_as("started_by", "the world was started by {1}").
reads_as("defines", "{1} defines the word {2}").

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

violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.

case_adds_line("a program that fakes an observation", "machine.mg", 'got("a step", "file", "nowhere").').
case_expects("a program that fakes an observation", "each_word_has_one_supplier").
case_answer("a program that fakes an observation", "false").

case_adds_line("a spec that observes for itself", "universe.mg", 'universe_file("ghost.txt").').
case_expects("a spec that observes for itself", "each_word_has_one_supplier").
case_answer("a spec that observes for itself", "false").

in_branch("universe_file", "the only knowledge is Datalog").
in_branch("known", "the only knowledge is Datalog").
reads_as("universe_file", "{1} is a file of the world").
reads_as("known", "{1} is known").

known(Path) :- language(Path, _).

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).

case_adds_line("a file that is not datalog", "notes.txt", "a note").
case_expects("a file that is not datalog", "the_only_knowledge_is_datalog").
case_answer("a file that is not datalog", "false").

in_branch("written_in", "file types").
in_branch("readable", "file types").
in_branch("language", "file types").
reads_as("written_in", "names ending in {1} are written in {2}").
reads_as("readable", "{1} is readable").
reads_as("language", "{1} is written in {2}").

written_in(".mg", "mangle").
written_in(".go", "go").
written_in("go.mod", "go module").
written_in("go.sum", "go checksums").
written_in(Entry, "sh") :- entry_point(Entry).
readable("mangle").

language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).

in_branch("has_comments", "comments").
in_branch("comment_in", "comments").
reads_as("has_comments", "{1} has comments").
reads_as("comment_in", "{1} has the comment {2}").

has_comments("mangle").
has_comments("go").
has_comments("sh").

violation("the_only_knowledge_is_datalog", Path) :- comment_in(Path, _).

case_adds_line("a comment", "machine.mg", "# a note").
case_expects("a comment", "the_only_knowledge_is_datalog").
case_answer("a comment", "false").

in_branch("answer", "the answer").
in_branch("exit_code", "the answer").
in_branch("output", "the answer").
in_branch("printed_in", "the answer").
in_branch("a_law_is_broken", "the answer").
in_branch("violation", "the answer").
in_branch("law", "the answer").
in_branch("unfired", "the answer").
in_branch("size", "the answer").
reads_as("answer", "the answer is {1}").
reads_as("exit_code", "the answer {1} exits with {2}").
reads_as("output", "{1} is printed").
reads_as("printed_in", "the world prints in {1}").
reads_as("a_law_is_broken", "a law is broken").
reads_as("violation", "{2} breaks {1}").
reads_as("law", "{1} is a law").
reads_as("unfired", "line {2} of {1} never fired").
reads_as("size", "{1} has {2} lines").

printed_in("english").
output("answer").
output("violation").
output("case_broke").
output("case_answered").
output("unfired").
output("size").

exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

a_law_is_broken() :- violation(_, _).
answer("false") :- a_law_is_broken().
answer("true") :- !a_law_is_broken().

case_answer("the world as it stands", "true").

case_adds_line("a world that cannot load", "universe.mg", "answer(").
case_answer("a world that cannot load", "broken").

in_branch("within", "cases").
in_branch("in_a_case", "cases").
in_branch("case", "cases").
in_branch("case_adds_line", "cases").
in_branch("case_expects", "cases").
in_branch("case_answer", "cases").
in_branch("case_broke", "cases").
in_branch("case_answered", "cases").
in_branch("missed", "cases").
in_branch("came_out_as_stated", "cases").
in_branch("expects_no_law", "cases").
in_branch("shown_failing", "cases").
reads_as("within", "the world runs within {1}").
reads_as("in_a_case", "the world is a case").
reads_as("case", "{1} is a case").
reads_as("case_adds_line", "{1} adds to {2} the line {3}").
reads_as("case_expects", "{1} must break {2}").
reads_as("case_answer", "{1} must answer {2}").
reads_as("case_broke", "{1} broke {2}").
reads_as("case_answered", "{1} answered {2}").
reads_as("missed", "{1} missed a law").
reads_as("came_out_as_stated", "{1} came out as stated").
reads_as("expects_no_law", "{1} expects a law nobody laid down").
reads_as("shown_failing", "{1} is shown failing").

in_a_case() :- within("a case").
case(Case) :- case_answer(Case, _).
missed(Case) :- case_expects(Case, Law), !case_broke(Case, Law).
came_out_as_stated(Case) :- case_answer(Case, Answer), case_answered(Case, Answer), !missed(Case).
expects_no_law(Case) :- case_expects(Case, Law), !law(Law).
shown_failing(Law) :- case_broke(_, Law).
shown_failing(Law) :- in_a_case(), case_expects(_, Law).

violation("every_law_is_shown_failing", Law) :- law(Law), !shown_failing(Law).
violation("every_case_comes_out_as_stated", Case) :- case(Case), !in_a_case(), !came_out_as_stated(Case).
violation("every_case_comes_out_as_stated", Case) :- expects_no_law(Case).

case_adds_line("a law with no case", "machine.mg", 'violation("a_law_with_no_case", Path) :- universe_file(Path), :string:ends_with(Path, ".txt").').
case_expects("a law with no case", "every_law_is_shown_failing").
case_answer("a law with no case", "false").

case_adds_line("a case that expects a law nobody laid down", "machine.mg", 'case_expects("a ghost case", "a_law_nobody_laid_down").').
case_expects("a case that expects a law nobody laid down", "every_case_comes_out_as_stated").
case_answer("a case that expects a law nobody laid down", "false").

in_branch("root", "understanding").
in_branch("part_of", "understanding").
in_branch("in_branch", "understanding").
in_branch("reads_as", "understanding").
in_branch("word", "understanding").
in_branch("placed", "understanding").
in_branch("has_a_reading", "understanding").
in_branch("reaches_the_root", "understanding").
reads_as("root", "{1} is the root").
reads_as("part_of", "the branch {1} is part of {2}").
reads_as("in_branch", "the word {1} belongs to the branch {2}").
reads_as("reads_as", "the word {1} reads as {2}").
reads_as("word", "{1} is a word").
reads_as("placed", "the word {1} is placed").
reads_as("has_a_reading", "the word {1} has a reading").
reads_as("reaches_the_root", "the branch {1} reaches the root").

word(Word) :- defines("universe.mg", Word).
word(Word) :- supplied_by(Word, _).
placed(Word) :- in_branch(Word, _).
has_a_reading(Word) :- reads_as(Word, _).
reaches_the_root(Branch) :- root(Branch).
reaches_the_root(Branch) :- part_of(Branch, Parent), reaches_the_root(Parent).

violation("every_word_is_understood", Word) :- word(Word), !placed(Word).
violation("every_word_is_understood", Word) :- word(Word), !has_a_reading(Word).
violation("every_word_is_understood", Word) :- in_branch(Word, One), in_branch(Word, Other), One != Other.
violation("every_branch_reaches_the_root", Branch) :- in_branch(_, Branch), !reaches_the_root(Branch).

case_adds_line("a word nobody explained", "universe.mg", 'lonely("a").').
case_expects("a word nobody explained", "every_word_is_understood").
case_answer("a word nobody explained", "false").

case_adds_line("a branch that hangs off nothing", "universe.mg", 'in_branch("lonely", "stray thoughts").').
case_expects("a branch that hangs off nothing", "every_branch_reaches_the_root").
case_answer("a branch that hangs off nothing", "false").
