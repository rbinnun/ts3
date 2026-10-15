old_copy_left() :- version("read copy", "copy.txt", "old").
expected() :- version("read copy", "copy.txt", "hello"), got("read copy", "content", "hello"), !old_copy_left().
