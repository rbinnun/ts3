within(Context) :- started_by(Context).

gives("list", "file").
gives("count lines", "lines").
gives("find comments", "comment").
gives("parse", "rule").
gives("read a rule", "head").
gives("read a rule", "first").
gives("read a rule", "uses").
gives("see what fired", "fired").
gives("try", "answer").
gives("try", "broke").
gives("try", "unfired").

does("list the folder", "list", ".").
listed(Path) :- does(Doing, "list", "."), got(Doing, "file", Path).
in_the_folder(Path) :- listed(Path).

counts(Doing, Path) :- listed(Path), Doing = fn:string:concat("count the lines of ", Path).
does(Doing, "count lines", Path) :- counts(Doing, Path).
size(Path, Lines) :- counts(Doing, Path), got(Doing, "lines", Lines).

looks_for_comments(Doing, Path, Language) :- listed(Path), language(Path, Language), has_comments(Language), Doing = fn:string:concat("look for comments in ", Path).
does(Doing, "find comments", fn:list(Path, Language)) :- looks_for_comments(Doing, Path, Language).
comment_in(Path, Text) :- looks_for_comments(Doing, Path, _), got(Doing, "comment", Text).

program(Path) :- spec(Path).
program(Path) :- workflow(Path).
parses(Doing, Path) :- program(Path), listed(Path), Doing = fn:string:concat("parse ", Path).
does(Doing, "parse", Path) :- parses(Doing, Path).
rule_in(Path, Rule) :- parses(Doing, Path), got(Doing, "rule", Rule).

does(Rule, "read a rule", Rule) :- rule_in(_, Rule).
rule_for(Rule, Word) :- rule_in(_, Rule), got(Rule, "head", Word).
rule_uses(Rule, Word) :- rule_in(_, Rule), got(Rule, "uses", Word).
rule_for_law(Rule, Law) :- rule_for(Rule, "violation"), got(Rule, "first", Law).
law(Law) :- rule_for_law(_, Law).
law_mentions(Law, Word) :- rule_for_law(Rule, Law), rule_uses(Rule, Word).
mentions(Word, Other) :- rule_for(Rule, Word), rule_uses(Rule, Other).
defines(Path, Word) :- rule_in(Path, Rule), rule_for(Rule, Word).

does(Change, "try", fn:list(Path, Line, Entry)) :- adds_line(Change, Path, Line), entry_point(Entry), !within("a change").
effect(Change, "a change") :- does(Change, "try", _).
answered(Change, Answer) :- does(Change, "try", _), got(Change, "answer", Answer).
broke(Change, Law) :- does(Change, "try", _), got(Change, "broke", Law).

sees(Doing, Path) :- parses(_, Path), Doing = fn:string:concat("see what fired in ", Path).
does(Doing, "see what fired", Path) :- sees(Doing, Path).
unfired_in(Change, Path, Rule) :- does(Change, "try", _), got(Change, "unfired", Where), :match_pair(Where, Path, Rule).
fired(Path, Rule) :- sees(Doing, Path), got(Doing, "fired", Rule).
fired(Path, Rule) :- answered(Change, Answer), Answer != "broken", rule_in(Path, Rule), !unfired_in(Change, Path, Rule).
unfired(Path, Rule) :- rule_in(Path, Rule), !fired(Path, Rule).
