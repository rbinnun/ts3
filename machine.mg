effect("looking around", "list").
effect("reading", "read").
effect("parsing", "parse").
effect("a case", "start").
effect("tracing", "trace").

within("a case") :- started_by("a case").

does("the world", "looking around").
universe_file(Path) :- got("the world", "file", Path).

reading(Path, Doing) :- universe_file(Path), Doing = ["reading", Path].
does(Doing, "reading") :- reading(_, Doing).
gives(Doing, "path", Path) :- reading(Path, Doing).
line_of(Path, Number, Text) :- reading(Path, Doing), got(Doing, "line", Line), Number = fn:list:get(Line, 0), Text = fn:list:get(Line, 1).
size(Path, Lines) :- reading(Path, Doing), got(Doing, "lines", Lines).

comment_syntax("mangle", '^(?:[^"\'#`]|"(?:[^"\\\\]|\\\\.)*"|\'(?:[^\'\\\\]|\\\\.)*\'|`[^`]*`)*#').
comment_syntax("go", '^(?:[^"\'/`]|/[^/*"\'`]|"(?:[^"\\\\]|\\\\.)*"|\'(?:[^\'\\\\]|\\\\.)*\'|`[^`]*`)*/[/*]').
comment_syntax("sh", '^(?:(?:[^"\'\\\\]|\\\\.|"(?:[^"\\\\]|\\\\.)*"|\'[^\']*\')*[\\s;&|()<>])?#').
comment_in(Path, Text) :- language(Path, Language), has_comments(Language), comment_syntax(Language, Syntax), line_of(Path, _, Text), :string:matches(Text, Syntax).

parsing(Path, Doing) :- language(Path, "mangle"), Doing = ["parsing", Path].
does(Doing, "parsing") :- parsing(_, Doing).
gives(Doing, "path", Path) :- parsing(Path, Doing).
clause_at(Path, Number, Line, Predicate) :- parsing(Path, Doing), got(Doing, "clause", Clause), Number = fn:list:get(Clause, 0), Line = fn:list:get(Clause, 1), Predicate = fn:list:get(Clause, 2).
argument_at(Path, Number, Position, Value) :- parsing(Path, Doing), got(Doing, "argument", Argument), Number = fn:list:get(Argument, 0), Position = fn:list:get(Argument, 1), Value = fn:list:get(Argument, 2).
defines(Path, Predicate) :- clause_at(Path, _, _, Predicate).

use_syntax("mangle", '^(?:[^"\'`]|"(?:[^"\\\\]|\\\\.)*"|\'(?:[^\'\\\\]|\\\\.)*\'|`[^`]*`)*:-(?:(?:[^"\'`]|"(?:[^"\\\\]|\\\\.)*"|\'(?:[^\'\\\\]|\\\\.)*\'|`[^`]*`)*[^A-Za-z0-9_.:"\'`])?', '\\(').
named(Name) :- program(Path), defines(Path, Name).
named(Name) :- word(Name).
uses(Path, Number, Other) :- program(Path), language(Path, Language), use_syntax(Language, Before, After), clause_at(Path, Number, Line, _), line_of(Path, Line, Text), named(Other), Syntax = fn:string:concat(Before, Other, After), :string:matches(Text, Syntax).
mentions(Word, Other) :- uses(Path, Number, Other), clause_at(Path, Number, _, Word), Word != "violation".
law_mentions(Law, Other) :- uses(Path, Number, Other), clause_at(Path, Number, _, "violation"), argument_at(Path, Number, 1, Law).

program(Path) :- source_of_truth(Path).
program(Path) :- machine_program(Path), universe_file(Path).
law(Law) :- program(Path), clause_at(Path, Number, _, "violation"), argument_at(Path, Number, 1, Law).

trying(Case, Doing) :- case(Case), !in_a_case(), Doing = ["trying", Case].
does(Doing, "a case") :- trying(_, Doing).
gives(Doing, "adds", Addition) :- trying(Case, Doing), case_adds_line(Case, Path, Line), Addition = [Path, Line].
case_answered(Case, Answer) :- trying(Case, Doing), got(Doing, "exit code", Code), exit_code(Answer, Code).
case_broke(Case, Law) :- trying(Case, Doing), got(Doing, "output", Fact), :match_cons(Fact, Predicate, Arguments), Predicate = "violation", :match_cons(Arguments, Law, _).

does("this run", "tracing").
fired(Path, Number) :- got("this run", "fired", Clause), Path = fn:list:get(Clause, 0), Number = fn:list:get(Clause, 1).
fired(Path, Number) :- trying(_, Doing), got(Doing, "fired", Clause), Path = fn:list:get(Clause, 0), Number = fn:list:get(Clause, 1).
unfired(Path, Line) :- clause_at(Path, Number, Line, _), !fired(Path, Number).

rule_for(Rule, Word) :- program(Path), clause_at(Path, _, Line, Word), Rule = [Path, Line].
rule_for_law(Rule, Law) :- program(Path), clause_at(Path, Number, Line, "violation"), argument_at(Path, Number, 1, Law), Rule = [Path, Line].
rule_uses(Rule, Word) :- uses(Path, Number, Word), clause_at(Path, Number, Line, _), Rule = [Path, Line].
