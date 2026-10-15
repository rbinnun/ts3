Decl place_count(Predicate, Count).
Decl middle_name(Predicate, Name).
Decl declares(Path, Predicate).
Decl defines(Path, Predicate).
Decl mentions(Path, Predicate).

label("Field").
label("Path").

wide(Predicate) :- place_count(Predicate, Count), Count > 3.
unlabelled_middle(Predicate) :- middle_name(Predicate, Name), !label(Name).
violation("every_fact_is_small", Predicate) :- wide(Predicate).
violation("every_fact_is_small", Predicate) :- unlabelled_middle(Predicate).

defined(Predicate) :- defines(Path, Predicate).
defined(Predicate) :- declares(Path, Predicate).
used(Predicate) :- mentions(Path, Predicate).
used(Predicate) :- read_by_the_judge(Predicate).
violation("every_predicate_is_defined", Where) :-
    mentions(Path, Predicate), !defined(Predicate), Where = fn:string:concat(Path, ": ", Predicate).
violation("every_predicate_is_used", Where) :-
    defines(Path, Predicate), !used(Predicate), Where = fn:string:concat(Path, ": ", Predicate).
