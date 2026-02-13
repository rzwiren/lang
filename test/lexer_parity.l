t0: (lex "a:1")~(lex2 "a:1")
t1: (lex "a:!10")~(lex2 "a:!10")
t2: (lex "b:5+a,4 5 6")~(lex2 "b:5+a,4 5 6")
t3: (lex "{a:1;b:2}")~(lex2 "{a:1;b:2}")
t4: (lex "(1;2;3)")~(lex2 "(1;2;3)")
t5: (lex "`abc")~(lex2 "`abc")
t6: (lex "$A")~(lex2 "$A")
t7: (lex "1 - 2")~(lex2 "1 - 2")
t8: (lex "1 -2 3")~(lex2 "1 -2 3")
t9: (lex "a:1//c")~(lex2 "a:1//c")

t0*t1*t2*t3*t4*t5*t6*t7*t8*t9
