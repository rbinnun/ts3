Decl violation(Law, Where).
Decl uses(World).
Decl verdict_of(World, Verdict).

broken() :- violation(Law, Where).
proven() :- !broken().
