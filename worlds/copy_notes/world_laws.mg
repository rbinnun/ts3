notes_read(Content) :- got("read notes", "content", Content).
copy_read(Content) :- got("read copy", "content", Content).
any_copy_read() :- copy_read(Content).

violation("the_copy_is_read_back", "read copy") :- !any_copy_read().
violation("the_copy_reads_as_the_notes", Content) :- copy_read(Content), !notes_read(Content).
