Decl wants(Doing, Effect).
Decl gives(Doing, Field, Value).
Decl done(Doing).
Decl got(Doing, Field, Value).
Decl file(Path, Content).

next_done(Doing) :- done(Doing).
next_done(Doing) :- wants(Doing, Effect).

next_got(Doing, Field, Value) :- got(Doing, Field, Value).
next_got(Doing, "content", Content) :- wants(Doing, "read_a_file"), gives(Doing, "path", Path), file(Path, Content).

written(Path) :- wants(Doing, "write_a_file"), gives(Doing, "path", Path).
next_file(Path, Content) :- file(Path, Content), !written(Path).
next_file(Path, Content) :- wants(Doing, "write_a_file"), gives(Doing, "path", Path), gives(Doing, "content", Content).
