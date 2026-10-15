does("read notes").
after("read notes", "start").
effect("read notes", "read_a_file").
target("read notes", "notes.txt").

does("copy notes") :- got("read notes", "content", Content).
after("copy notes", "read notes").
effect("copy notes", "write_a_file").
target("copy notes", "copy.txt").
gives("copy notes", "content", Content) :- got("read notes", "content", Content).

does("read copy") :- does("copy notes").
after("read copy", "copy notes").
effect("read copy", "read_a_file").
target("read copy", "copy.txt").

tells(Line) :- got("read copy", "content", Content), Line = fn:string:concat("the copy says: ", Content).
