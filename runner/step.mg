Decl done(Doing).
Decl got(Doing, Content).
Decl file(Path, Content).

next_done(Doing) :- done(Doing).
next_done(Doing) :- wants(Doing, Effect, Path, Content).

next_got(Doing, Content) :- got(Doing, Content).
next_got(Doing, Content) :- wants(Doing, "read_a_file", Path, Given), file(Path, Content).

written(Path) :- wants(Doing, "write_a_file", Path, Content).
next_file(Path, Content) :- file(Path, Content), !written(Path).
next_file(Path, Content) :- wants(Doing, "write_a_file", Path, Content).
