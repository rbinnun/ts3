uses("language_contract").
uses("copy_notes").

violation("every_child_world_is_proven", World) :- uses(World), !verdict_of(World, "proven").
