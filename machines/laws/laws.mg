wide(Predicate) :- place_count(Predicate, Count), Count > 3.
unlabelled_middle(Predicate) :- middle_name(Predicate, Name), Name != "Field".
violation("every_fact_is_small", Predicate) :- wide(Predicate).
violation("every_fact_is_small", Predicate) :- unlabelled_middle(Predicate).
