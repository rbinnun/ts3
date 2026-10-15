uses("language_contract").
uses("copy_notes").

Decl universe_file(Path).

used_outside_the_judge("run.me").
plain_file("judge/machine/go.mod").
plain_file("judge/machine/go.sum").

mangle_program(Path) :- universe_file(Path), :string:ends_with(Path, ".mg").
go_program(Path) :- universe_file(Path), :string:ends_with(Path, ".go").
judge_program(Path) :- go_program(Path), :string:starts_with(Path, "judge/machine/").
source_program(Path) :- go_program(Path), :string:starts_with(Path, "sources/").
source_program(Path) :- go_program(Path), :string:starts_with(Path, "worlds/"), :string:contains(Path, "/sources/").

file_in_place(Path) :- mangle_program(Path).
file_in_place(Path) :- judge_program(Path).
file_in_place(Path) :- source_program(Path).
file_in_place(Path) :- plain_file(Path).
file_in_place(Path) :- used_outside_the_judge(Path).

file_of_a_used_world(Path) :-
    universe_file(Path), uses(World), Folder = fn:string:concat("worlds/", World, "/"), :string:starts_with(Path, Folder).

violation("every_child_world_is_proven", World) :- uses(World), !verdict_of(World, "proven").
violation("every_file_has_its_place", Path) :- universe_file(Path), !file_in_place(Path).
violation("every_world_folder_is_used", Path) :-
    universe_file(Path), :string:starts_with(Path, "worlds/"), !file_of_a_used_world(Path).
