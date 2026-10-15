Decl file(Path, Content).
Decl place_count(Predicate, Count).
Decl middle_name(Predicate, Name).

next_got(Doing, "content", Content) :- wants(Doing, "read_a_file"), gives(Doing, "path", Path), file(Path, Content).

written(Path) :- wants(Doing, "write_a_file"), gives(Doing, "path", Path).
next_file(Path, Content) :- file(Path, Content), !written(Path).
next_file(Path, Content) :- wants(Doing, "write_a_file"), gives(Doing, "path", Path), gives(Doing, "content", Content).

next_place_count(Predicate, Count) :- place_count(Predicate, Count).
next_middle_name(Predicate, Name) :- middle_name(Predicate, Name).
