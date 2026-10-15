wants("read notes", "read_a_file") :- !done("read notes").
gives("read notes", "path", "notes.txt").

wants("copy notes", "write_a_file") :- got("read notes", "content", Content), !done("copy notes").
gives("copy notes", "path", "copy.txt").
gives("copy notes", "content", Content) :- got("read notes", "content", Content).

tells(Line) :- got("read notes", "content", Content), Line = fn:string:concat("notes say: ", Content).
