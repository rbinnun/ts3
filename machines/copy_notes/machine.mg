wants("read notes", "read_a_file", "notes.txt", "") :- !done("read notes").
wants("copy notes", "write_a_file", "copy.txt", Content) :- got("read notes", Content), !done("copy notes").
tells(Line) :- got("read notes", Content), Line = fn:string:concat("notes say: ", Content).
