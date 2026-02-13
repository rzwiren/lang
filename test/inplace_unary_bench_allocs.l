n:100000

// Unary negation chain: in-place should reuse the same vector each time.
b0: bench (10;"{[] -(-(-(-(!100000)))) }[]";1)
// Force fresh allocations by pinning intermediates in-scope via assignment (rc>0).
b1: bench (10;"{[] a:(!100000); a:-a; a:-a; a:-a; a:-a; a }[]";1)

// Bitwise-not chain: same idea.
c0: bench (10;"{[] bnot(bnot(bnot(bnot(!100000)))) }[]";1)
c1: bench (10;"{[] a:(!100000); a:bnot a; a:bnot a; a:bnot a; a:bnot a; a }[]";1)

t0: 4~#b0
t1: 4~#b1
t2: 4~#c0
t3: 4~#c1

u0: b0@2
u1: b1@2
v0: c0@2
v1: c1@2

t4: 1~u1>u0
t5: 1~u1>u0+u0
t6: 1~v1>v0
t7: 1~v1>v0+v0

t8: n~#(b0@1)
t9: n~#(c0@1)
tA: 3~@(b0@1)
tB: 3~@(c0@1)

t0*t1*t2*t3*t4*t5*t6*t7*t8*t9*tA*tB
