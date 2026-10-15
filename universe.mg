mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").

entry_point("run.me").
machinery_ending(".go").
machinery_ending("go.mod").
machinery_ending("go.sum").

read_by_the_machinery("does").
read_by_the_machinery("effect").
read_by_the_machinery("gives").
read_by_the_machinery("tells").
read_by_the_machinery("violation").

label("Field").
label("Path").

Decl started_by(Effect).
Decl got(Doing, Field, Value).
Decl declares(Path, Predicate).
Decl defines(Path, Predicate).
Decl mentions(Path, Predicate).
Decl place_count(Predicate, Count).
Decl middle_name(Predicate, Name).
Decl law_stated(Path, Law).
Decl comment_line(Path, Line).

within_a_case() :- started_by("run_a_case").

does("list the universe").
effect("list the universe", "list_a_folder").
gives("list the universe", "folder", ".").

universe_file(Path) :- got("list the universe", "file", Path).

mangle_program(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").
machinery_file(Path) :- universe_file(Path), entry_point(Path).
machinery_file(Path) :- universe_file(Path), machinery_ending(Ending), :string:ends_with(Path, Ending).
go_module(Path) :- universe_file(Path), :string:ends_with(Path, "go.mod").
code_file(Path) :- machinery_file(Path), entry_point(Path).
code_file(Path) :- machinery_file(Path), :string:ends_with(Path, ".go").

breaking_up(Doing, Path) :- mangle_program(Path), Doing = fn:string:concat("break up ", Path).
finding_comments(Doing, Path) :- mangle_program(Path), Doing = fn:string:concat("find comments in ", Path).
finding_comments(Doing, Path) :- code_file(Path), Doing = fn:string:concat("find comments in ", Path).
reading_requirements(Doing, Path) :- go_module(Path), Doing = fn:string:concat("read requirements of ", Path).
running(Doing, Case) :- case(Case), !within_a_case(), Doing = fn:string:concat("run the case ", Case).

does(Doing) :- breaking_up(Doing, _).
does(Doing) :- finding_comments(Doing, _).
does(Doing) :- reading_requirements(Doing, _).
does(Doing) :- running(Doing, _).

effect(Doing, "break_up_a_program") :- breaking_up(Doing, _).
effect(Doing, "find_comments") :- finding_comments(Doing, _).
effect(Doing, "read_requirements") :- reading_requirements(Doing, _).
effect(Doing, "run_a_case") :- running(Doing, _).

gives(Doing, "path", Path) :- breaking_up(Doing, Path).
gives(Doing, "path", Path) :- finding_comments(Doing, Path).
gives(Doing, "path", Path) :- reading_requirements(Doing, Path).
gives(Doing, Path, Content) :- running(Doing, Case), case_file(Case, Path, Content).
gives(Doing, "copy", Path) :- running(Doing, Case), case_copies(Case, Path).

case(Case) :- case_exits(Case, _).
ran(Case) :- running(Doing, Case), got(Doing, "exited", _).
printed(Case, Line) :- running(Doing, Case), got(Doing, "printed", Line).
missed_a_line(Case) :- ran(Case), case_prints(Case, Line), !printed(Case, Line).
printed_an_extra_line(Case) :- printed(Case, Line), !case_prints(Case, Line).
exited_otherwise(Case) :- running(Doing, Case), got(Doing, "exited", Code), case_exits(Case, Expected), Code != Expected.
came_out_as_stated(Case) :- ran(Case), !missed_a_line(Case), !printed_an_extra_line(Case), !exited_otherwise(Case).
differed(Case) :- ran(Case), !came_out_as_stated(Case).

tells(Line) :- came_out_as_stated(Case), !case_differs(Case), Line = fn:string:concat(Case, " came out as stated").
tells(Line) :- differed(Case), case_differs(Case), Line = fn:string:concat(Case, " differed as stated").

violation("the_only_knowledge_is_datalog", Path) :- universe_file(Path), !mangle_program(Path), !machinery_file(Path).
violation("the_only_knowledge_is_datalog", Path) :- comment_line(Path, _).

defined(Predicate) :- defines(_, Predicate).
defined(Predicate) :- declares(_, Predicate).
used(Predicate) :- mentions(_, Predicate).
used(Predicate) :- read_by_the_machinery(Predicate).
has_a_labelled_middle(Predicate) :- middle_name(Predicate, Name), label(Name).

violation("every_piece_of_knowledge_is_understood", Predicate) :- place_count(Predicate, Count), Count > 3.
violation("every_piece_of_knowledge_is_understood", Predicate) :- place_count(Predicate, 3), !has_a_labelled_middle(Predicate).
violation("every_piece_of_knowledge_is_understood", Predicate) :- middle_name(Predicate, Name), !label(Name).
violation("every_piece_of_knowledge_is_understood", Predicate) :- mentions(_, Predicate), !defined(Predicate).
violation("every_piece_of_knowledge_is_understood", Predicate) :- defined(Predicate), !used(Predicate).

law_shown_failing(Law) :- law_stated(_, Law), case_prints(_, Line), Start = fn:string:concat("violation(\"", Law, "\""), :string:starts_with(Line, Start).

violation("every_piece_of_knowledge_is_proven", Law) :- law_stated(_, Law), !law_shown_failing(Law).
violation("every_piece_of_knowledge_is_proven", Case) :- case(Case), !within_a_case(), !came_out_as_stated(Case), !case_differs(Case).
violation("every_piece_of_knowledge_is_proven", Case) :- case_differs(Case), !within_a_case(), !differed(Case).

runs_the_pinned_mangle(Path) :- reading_requirements(Doing, Path), mangle_module(Field), mangle_version(Version), got(Doing, Field, Version).

violation("the_machinery_runs_the_pinned_mangle", Path) :- go_module(Path), !runs_the_pinned_mangle(Path).

case_file("a told line is printed", "hello.mg", `tells("hello").`).
case_prints("a told line is printed", `tells("hello")`).
case_exits("a told line is printed", 0).

case_file("a broken law is printed and exits one", "law.mg", `violation("a_law", "here").`).
case_prints("a broken law is printed and exits one", `violation("a_law","here")`).
case_exits("a broken law is printed and exits one", 1).

case_file("the programs of a folder run as one", "a.mg", `said("a").`).
case_file("the programs of a folder run as one", "b.mg", `tells(Word) :- said(Word).`).
case_file("the programs of a folder run as one", "world/c.mg", `said("c").`).
case_prints("the programs of a folder run as one", `tells("a")`).
case_exits("the programs of a folder run as one", 0).

case_file("a case says what started it", "start.mg", `Decl started_by(Effect).
tells(Effect) :- started_by(Effect).`).
case_prints("a case says what started it", `tells("run_a_case")`).
case_exits("a case says what started it", 0).

case_file("an unknown effect stops the run", "step.mg", `does("step").
effect("step", "no_such_effect").
tells("never").`).
case_exits("an unknown effect stops the run", 2).

case_file("a broken program stops the run", "broken.mg", `tells("never"`).
case_exits("a broken program stops the run", 2).

case_file("a folder is listed", "list.mg", `Decl got(Doing, Field, Value).
does("list").
effect("list", "list_a_folder").
gives("list", "folder", ".").
tells(Path) :- got("list", "file", Path).`).
case_file("a folder is listed", "world/deep/notes.txt", `a note`).
case_file("a folder is listed", ".hidden/notes.txt", `a note`).
case_file("a folder is listed", "world/.notes.txt", `a note`).
case_prints("a folder is listed", `tells("list.mg")`).
case_prints("a folder is listed", `tells("world/deep/notes.txt")`).
case_exits("a folder is listed", 0).

case_file("a program is broken up", "break.mg", `Decl declares(Path, Predicate).
Decl defines(Path, Predicate).
Decl mentions(Path, Predicate).
Decl place_count(Predicate, Count).
Decl middle_name(Predicate, Name).
Decl law_stated(Path, Law).
does("break").
effect("break", "break_up_a_program").
gives("break", "path", "world/sample.mg").
tells("declares", Path, Predicate) :- declares(Path, Predicate).
tells("defines", Path, Predicate) :- defines(Path, Predicate).
tells("mentions", Path, Predicate) :- mentions(Path, Predicate).
tells("place_count", Predicate, Count) :- place_count(Predicate, Count).
tells("middle_name", Predicate, Name) :- middle_name(Predicate, Name).
tells("law_stated", Path, Law) :- law_stated(Path, Law).`).
case_file("a program is broken up", "world/sample.mg", `Decl pair(Left, Path, Right).
pair("a", "b", "c").
violation("a_law", Left) :- pair(Left, Path, Right), !lonely(Right), :string:starts_with(Left, "a").`).
case_prints("a program is broken up", `tells("declares","world/sample.mg","pair")`).
case_prints("a program is broken up", `tells("defines","world/sample.mg","pair")`).
case_prints("a program is broken up", `tells("defines","world/sample.mg","violation")`).
case_prints("a program is broken up", `tells("mentions","world/sample.mg","pair")`).
case_prints("a program is broken up", `tells("mentions","world/sample.mg","lonely")`).
case_prints("a program is broken up", `tells("place_count","pair",3)`).
case_prints("a program is broken up", `tells("place_count","violation",2)`).
case_prints("a program is broken up", `tells("place_count","lonely",1)`).
case_prints("a program is broken up", `tells("middle_name","pair","Path")`).
case_prints("a program is broken up", `tells("law_stated","world/sample.mg","a_law")`).
case_exits("a program is broken up", 0).

case_file("comments are found", "find.mg", `Decl comment_line(Path, Line).
does("find in mangle").
effect("find in mangle", "find_comments").
gives("find in mangle", "path", "world/a.mg").
does("find in go").
effect("find in go", "find_comments").
gives("find in go", "path", "world/b.go").
does("find in the entry point").
effect("find in the entry point", "find_comments").
gives("find in the entry point", "path", "run.me").
tells(Path, Line) :- comment_line(Path, Line).`).
case_file("comments are found", "world/a.mg", `a("# not a comment").
# a comment
b(1). # a comment
c('#').`).
case_file("comments are found", "world/b.go", `package b

// a comment
var s = "// not a comment"

/* a comment
over two lines */
var t = 1 // a comment
`).
case_file("comments are found", "run.me", `#!/bin/sh
# a comment
echo "# not a comment"
`).
case_prints("comments are found", `tells("world/a.mg",2)`).
case_prints("comments are found", `tells("world/a.mg",3)`).
case_prints("comments are found", `tells("world/b.go",3)`).
case_prints("comments are found", `tells("world/b.go",6)`).
case_prints("comments are found", `tells("world/b.go",7)`).
case_prints("comments are found", `tells("world/b.go",8)`).
case_prints("comments are found", `tells("run.me",2)`).
case_exits("comments are found", 0).

case_file("requirements are read", "read.mg", `Decl got(Doing, Field, Value).
does("read").
effect("read", "read_requirements").
gives("read", "path", "world/go.mod").
tells(Module, Version) :- got("read", Module, Version).`).
case_file("requirements are read", "world/go.mod", `module example

go 1.22

require codeberg.org/TauCeti/mangle-go v0.7.0

require (
	example.com/first v1.2.3 // indirect
	example.com/second v0.0.1
)
`).
case_prints("requirements are read", `tells("codeberg.org/TauCeti/mangle-go","v0.7.0")`).
case_prints("requirements are read", `tells("example.com/first","v1.2.3")`).
case_prints("requirements are read", `tells("example.com/second","v0.0.1")`).
case_exits("requirements are read", 0).

case_file("a case that differs", "hello.mg", `tells("hello").`).
case_prints("a case that differs", `tells("goodbye")`).
case_exits("a case that differs", 0).
case_differs("a case that differs").

case_copies("a universe without breaks", "universe.mg").
case_exits("a universe without breaks", 0).

case_copies("a file that is not datalog", "universe.mg").
case_file("a file that is not datalog", "notes.txt", `a note`).
case_prints("a file that is not datalog", `violation("the_only_knowledge_is_datalog","notes.txt")`).
case_exits("a file that is not datalog", 1).

case_copies("a comment", "universe.mg").
case_file("a comment", "world/note.mg", `tells("seen").
# a note`).
case_prints("a comment", `violation("the_only_knowledge_is_datalog","world/note.mg")`).
case_exits("a comment", 1).

case_copies("a wide fact", "universe.mg").
case_file("a wide fact", "world/wide.mg", `wide("a", "b", "c", "d").
tells("seen") :- wide(_, _, _, _).`).
case_prints("a wide fact", `violation("every_piece_of_knowledge_is_understood","wide")`).
case_exits("a wide fact", 1).

case_copies("an unlabelled middle", "universe.mg").
case_file("an unlabelled middle", "world/pair.mg", `pair("a", "b", "c").
tells(Middle) :- pair(_, Middle, _).`).
case_prints("an unlabelled middle", `violation("every_piece_of_knowledge_is_understood","pair")`).
case_exits("an unlabelled middle", 1).

case_copies("an undefined predicate", "universe.mg").
case_file("an undefined predicate", "world/nowhere.mg", `tells("seen") :- nowhere().`).
case_prints("an undefined predicate", `violation("every_piece_of_knowledge_is_understood","nowhere")`).
case_exits("an undefined predicate", 1).

case_copies("an unused predicate", "universe.mg").
case_file("an unused predicate", "world/lonely.mg", `lonely("a").`).
case_prints("an unused predicate", `violation("every_piece_of_knowledge_is_understood","lonely")`).
case_exits("an unused predicate", 1).

case_copies("a law never shown failing", "universe.mg").
case_file("a law never shown failing", "world/law.mg", `violation("an_unshown_law", Path) :- universe_file(Path), :string:ends_with(Path, ".txt").`).
case_prints("a law never shown failing", `violation("every_piece_of_knowledge_is_proven","an_unshown_law")`).
case_exits("a law never shown failing", 1).

case_copies("an older mangle", "universe.mg").
case_file("an older mangle", "go.mod", `module example

go 1.22

require codeberg.org/TauCeti/mangle-go v0.6.0
`).
case_prints("an older mangle", `violation("the_machinery_runs_the_pinned_mangle","go.mod")`).
case_exits("an older mangle", 1).
