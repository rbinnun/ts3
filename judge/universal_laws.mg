Decl violation(Law, Where).
Decl uses(World).
Decl verdict_of(World, Verdict).

broken() :- violation(Law, Where).
proven() :- !broken().

read_by_the_judge("proven").
read_by_the_judge("violation").
read_by_the_judge("uses").
read_by_the_judge("tells").
read_by_the_judge("keeps").
