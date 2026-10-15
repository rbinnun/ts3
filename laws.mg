Decl place_count(Predicate, Count).
Decl middle_name(Predicate, Name).

label("Field").
label("Path").

wide(Predicate) :- place_count(Predicate, Count), Count > 3.
unlabelled_middle(Predicate) :- middle_name(Predicate, Name), !label(Name).
violation("every_fact_is_small", Predicate) :- wide(Predicate).
violation("every_fact_is_small", Predicate) :- unlabelled_middle(Predicate).

broken() :- violation(Law, Predicate).
kept() :- !broken().
