Decl wants(Doing, Effect).
Decl gives(Doing, Field, Value).
Decl done(Doing).
Decl got(Doing, Field, Value).

next_done(Doing) :- done(Doing).
next_done(Doing) :- wants(Doing, Effect).
next_got(Doing, Field, Value) :- got(Doing, Field, Value).
