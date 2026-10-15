Decl does(Doing).
Decl after(Doing, Previous).
Decl effect(Doing, Effect).
Decl target(Doing, Path).
Decl gives(Doing, Field, Value).
Decl file(Path, Content).

version("start", Path, Content) :- file(Path, Content).
writes(Doing, Path) :- effect(Doing, "write_a_file"), target(Doing, Path).
version(Doing, Path, Content) :- does(Doing), after(Doing, Previous), version(Previous, Path, Content), !writes(Doing, Path).
version(Doing, Path, Content) :- does(Doing), writes(Doing, Path), gives(Doing, "content", Content).

got(Doing, "content", Content) :-
    does(Doing), effect(Doing, "read_a_file"), target(Doing, Path), after(Doing, Previous), version(Previous, Path, Content).
