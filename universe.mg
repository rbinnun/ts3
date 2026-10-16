reads_as("entry_point", "the world is started with {1}").
reads_as("read_by_the_machinery", "the machinery reads the word {1}").

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
read_by_the_machinery("output_file").
read_by_the_machinery("title").
read_by_the_machinery("shows").
read_by_the_machinery("shows_case").
read_by_the_machinery("opens_into").
read_by_the_machinery("explained_by").
read_by_the_machinery("negation").

reads_as("machine_program", "{1} is a machine program").
reads_as("leg", "{1} is a leg").
reads_as("belongs_to", "{1} belongs to the leg {2}").
reads_as("in_a_leg", "{1} is in a leg").
reads_as("source_of_truth", "{1} is the source of truth").

source_of_truth("universe.mg").
machine_program("machine.mg").
leg("universe.mg").
leg("machine.mg").
leg("the machinery").
leg("the outputs").

belongs_to("universe.mg", "universe.mg").
belongs_to(Path, "machine.mg") :- machine_program(Path).
belongs_to(Path, "the machinery") :- language(Path, Language), !readable(Language), !output_file(Path).
belongs_to(Path, "the outputs") :- output_file(Path).
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
supplied_by("mentions", "machine.mg").
supplied_by("law_mentions", "machine.mg").
supplied_by("rule_for", "machine.mg").
supplied_by("rule_for_law", "machine.mg").
supplied_by("rule_uses", "machine.mg").

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
Decl mentions(Word, Other).
Decl law_mentions(Law, Word).
Decl rule_for(Rule, Word).
Decl rule_for_law(Rule, Law).
Decl rule_uses(Rule, Word).

violation("each_word_has_one_supplier", Path) :- defines(Path, Predicate), supplied_by(Predicate, Supplier), Supplier != Path.

case_adds_line("a program that fakes an observation", "machine.mg", 'got("a step", "file", "nowhere").').
case_expects("a program that fakes an observation", "each_word_has_one_supplier").
case_answer("a program that fakes an observation", "false").

case_adds_line("a spec that observes for itself", "universe.mg", 'universe_file("ghost.txt").').
case_expects("a spec that observes for itself", "each_word_has_one_supplier").
case_answer("a spec that observes for itself", "false").

reads_as("universe_file", "{1} is a file of the world").
reads_as("known", "{1} is known").

known(Path) :- language(Path, _).

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !known(Path).

case_adds_line("a file that is not datalog", "notes.txt", "a note").
case_expects("a file that is not datalog", "the_only_knowledge_is_datalog").
case_answer("a file that is not datalog", "false").

reads_as("written_in", "names ending in {1} are written in {2}").
reads_as("readable", "{1} is readable").
reads_as("language", "{1} is written in {2}").

written_in(".mg", "mangle").
written_in(".go", "go").
written_in("go.mod", "go module").
written_in("go.sum", "go checksums").
written_in(".html", "html").
written_in(Entry, "sh") :- entry_point(Entry).
readable("mangle").

language(Path, Language) :- universe_file(Path), written_in(Ending, Language), :string:ends_with(Path, Ending).

reads_as("has_comments", "{1} has comments").
reads_as("comment_in", "{1} has the comment {2}").

has_comments("mangle").
has_comments("go").
has_comments("sh").

violation("the_only_knowledge_is_datalog", Path) :- comment_in(Path, _).

case_adds_line("a comment", "machine.mg", "# a note").
case_expects("a comment", "the_only_knowledge_is_datalog").
case_answer("a comment", "false").

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
output("rests_on").

exit_code("true", 0).
exit_code("false", 1).
exit_code("broken", 2).

a_law_is_broken() :- violation(_, _).
answer("false") :- a_law_is_broken().
answer("true") :- !a_law_is_broken().

case_answer("the world as it stands", "true").

case_adds_line("a world that cannot load", "universe.mg", "answer(").
case_answer("a world that cannot load", "broken").

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

reads_as("reads_as", "the word {1} reads as {2}").
reads_as("word", "{1} is a word").
reads_as("has_a_reading", "the word {1} has a reading").
reads_as("mentions", "a rule for {1} uses {2}").
reads_as("law_mentions", "a rule for the law {1} uses {2}").
reads_as("rests_on", "{1} rests on {2}").
reads_as("reaches_the_outside", "{1} reaches the outside").

word(Word) :- defines("universe.mg", Word).
word(Word) :- supplied_by(Word, _).
has_a_reading(Word) :- reads_as(Word, _).
rests_on(Word, Other) :- mentions(Word, Other).
rests_on("violation", Law) :- law(Law).
rests_on("output", Word) :- output(Word).
rests_on(Law, Word) :- law_mentions(Law, Word).
reaches_the_outside(Word) :- read_by_the_machinery(Word).
reaches_the_outside(Other) :- rests_on(Word, Other), reaches_the_outside(Word).

violation("every_word_is_understood", Word) :- word(Word), !has_a_reading(Word).
violation("every_word_is_understood", Word) :- word(Word), !reaches_the_outside(Word).

case_adds_line("a word nobody explained", "universe.mg", 'lonely("a").').
case_expects("a word nobody explained", "every_word_is_understood").
case_answer("a word nobody explained", "false").

reads_as("output_file", "{1} is written by the machine on every run").
reads_as("rule_for", "the rule {1} defines {2}").
reads_as("rule_for_law", "the rule {1} lays down {2}").
reads_as("rule_uses", "the rule {1} uses {2}").
reads_as("concept", "{1} is a concept").
reads_as("title", "{1} is titled {2}").
reads_as("titled", "{1} has a title").
reads_as("negation", "{1} reads {2} when it is not so").
reads_as("shows", "the concept {1} is made of the rule {2}").
reads_as("shows_case", "the concept {1} is shown by {2}").
reads_as("opens_into", "the rule {1} opens into {2}").
reads_as("explained_by", "{1} is explained by the rule {2}").
reads_as("expects_a_law", "{1} expects a law to break").

output_file("universe.html").

concept("the answer").
concept(Law) :- law(Law).
title("the answer", "The answer").
title("the_only_knowledge_is_datalog", "The only knowledge is Datalog").
title("each_word_has_one_supplier", "Each word has one supplier").
title("every_file_belongs_to_a_leg", "Every file belongs to a leg").
title("the_world_sees_itself", "The world sees itself").
title("every_law_is_shown_failing", "Every law is shown failing").
title("every_case_comes_out_as_stated", "Every case comes out as stated").
title("every_word_is_understood", "Every word is understood").
title("every_concept_has_a_title", "Every concept has a title").
titled(Concept) :- title(Concept, _).

negation("is", "is not").
negation("are", "are not").
negation("has", "does not have").
negation("broke", "did not break").
negation("answered", "did not answer").
negation("defines", "does not define").
negation("uses", "does not use").
negation("reaches", "does not reach").
negation("expects", "does not expect").
negation("came out", "did not come out").
negation("missed a", "missed no").

expects_a_law(Case) :- case_expects(Case, _).
shows("the answer", Rule) :- rule_for(Rule, "answer").
shows(Law, Rule) :- concept(Law), rule_for_law(Rule, Law).
shows_case("the answer", Case) :- case_answer(Case, _), !expects_a_law(Case).
shows_case(Law, Case) :- concept(Law), case_expects(Case, Law).
opens_into(Rule, Word) :- rule_uses(Rule, Word).
explained_by(Word, Rule) :- rule_for(Rule, Word).

violation("every_concept_has_a_title", Concept) :- concept(Concept), !titled(Concept).

case_adds_line("a concept with no title", "machine.mg", 'violation("an_untitled_law", "here") :- universe_file("nowhere").').
case_expects("a concept with no title", "every_concept_has_a_title").
case_answer("a concept with no title", "false").
