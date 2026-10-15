wants("read the programs", "read_the_programs") :- !done("read the programs").
gives("read the programs", "folder", ".").

any_violation() :- violation(Law, Predicate).
fails(Reason) :- violation(Law, Predicate), Reason = fn:string:concat(Law, ": ", Predicate).
tells("every program keeps the laws") :- done("read the programs"), !any_violation().
