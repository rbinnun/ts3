does("list the folder", "list", ".").

in_the_folder(Path) :- does(Step, "list", _), got(Step, "file", Path).

does(Step, "count lines", Path) :- in_the_folder(Path) |> let Step = fn:string:concat("count the lines of ", Path).

size(Path, Lines) :- does(Step, "count lines", Path), got(Step, "lines", Lines).

does(Step, "find comments", Source) :- language(Path, Language), has_comments(Language) |> let Step = fn:string:concat("find the comments in ", Path), let Source = fn:pair(Path, Language).

comment_in(Path, Text) :- does(Step, "find comments", Source), :match_pair(Source, Path, _), got(Step, "comment", Text).

does(Step, "parse", Path) :- language(Path, "mangle") |> let Step = fn:string:concat("parse ", Path).

rule_in(Path, Rule) :- does(Step, "parse", Path), got(Step, "rule", Rule).

does(Step, "read a rule", Rule) :- rule_in(_, Rule) |> let Step = fn:string:concat("read ", Rule).

rule_for(Rule, Word) :- does(Step, "read a rule", Rule), got(Step, "head", Word).

rule_uses(Rule, Word) :- does(Step, "read a rule", Rule), got(Step, "uses", Word).

defines(Path, Word) :- rule_in(Path, Rule), rule_for(Rule, Word).

in_the_program(Path) :- spec(Path), in_the_folder(Path).
in_the_program(Path) :- workflow(Path), in_the_folder(Path).

mentions(Word, Other) :- in_the_program(Path), rule_in(Path, Rule), rule_for(Rule, Word), rule_uses(Rule, Other).

rule_for_law(Rule, Law) :- in_the_program(Path), rule_in(Path, Rule), rule_for(Rule, "violation"), does(Step, "read a rule", Rule), got(Step, "first argument", Law).

law(Law) :- rule_for_law(_, Law).

law_mentions(Law, Word) :- rule_for_law(Rule, Law), rule_uses(Rule, Word).

within("a change") :- started_by("try").

does(Change, "try", Effect) :- adds_line(Change, Path, Line), !within("a change") |> let Effect = fn:pair(Path, Line).

broke(Change, Law) :- does(Change, "try", _), got(Change, "broke", Law).

answered(Change, Answer) :- does(Change, "try", _), got(Change, "conforms", Answer).

does(Step, "see what fired", Path) :- in_the_program(Path) |> let Step = fn:string:concat("see what fired in ", Path).

fired(Path, Rule) :- does(Step, "see what fired", Path), got(Step, "fired", Rule).

unfired_in(Change, Path, Rule) :- does(Change, "try", _), got(Change, "unfired", Where), :match_pair(Where, Path, Rule).

fired_in_a_change(Path, Rule) :- unfired_in(Change, _, _), rule_in(Path, Rule), !unfired_in(Change, Path, Rule).

unfired(Path, Rule) :- in_the_program(Path), rule_in(Path, Rule), !fired(Path, Rule), !fired_in_a_change(Path, Rule).
