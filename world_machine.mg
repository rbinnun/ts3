Decl got(Doing, Field, Value).

does("list the universe").
effect("list the universe", "list_a_folder").
target("list the universe", ".").

loaded_file("judge/machine/load.mg").
universe_file(Path) :- loaded_file(Path).
universe_file(Path) :- got("list the universe", "file", Path).

program_file(Path) :- universe_file(Path), :string:ends_with(Path, ".mg"), !loaded_file(Path).
code_file(Path) :- program_file(Path).
code_file(Path) :- universe_file(Path), :string:ends_with(Path, ".go").

breaking_up(Doing, Path) :- program_file(Path), Doing = fn:string:concat("break up ", Path).
does(Doing) :- breaking_up(Doing, Path).
effect(Doing, "break_up_a_program") :- breaking_up(Doing, Path).
target(Doing, Path) :- breaking_up(Doing, Path).

finding_comments(Doing, Path) :- code_file(Path), Doing = fn:string:concat("find comments in ", Path).
does(Doing) :- finding_comments(Doing, Path).
effect(Doing, "find_comments") :- finding_comments(Doing, Path).
target(Doing, Path) :- finding_comments(Doing, Path).

keeps("universe_file").
keeps("comment_line").
keeps("declares").
keeps("defines").
keeps("mentions").
keeps("place_count").
keeps("middle_name").
