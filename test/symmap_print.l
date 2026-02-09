// symtab/symmap are bootstrapped and consistent with each other.
ids0:symmap@("symtab")
ids1:symmap@("symmap")
id0:ids0@0
id1:ids1@0
t0: "symtab"~symtab@id0
t1: "symmap"~symtab@id1

t0*t1
