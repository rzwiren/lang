// References (identifiers) are interned into symtab/symmap at lex time.
// Also verifies that dictionary keys created via identifier assignment are symbols.
d:{a:1}
t0: 1~d@`a

a:1
ids:symmap@,"a"
id:ids@0
t1: "a"~symtab@id
t2: 1~a

t0*t1*t2
