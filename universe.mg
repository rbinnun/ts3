mangle_module("codeberg.org/TauCeti/mangle-go").
mangle_version("v0.7.0").
entry_point("run.me").

Decl got(Doing, Field, Value).

does("list the universe").
effect("list the universe", "list_a_folder").
gives("list the universe", "folder", ".").

tells(Path) :- got("list the universe", "file", Path).
