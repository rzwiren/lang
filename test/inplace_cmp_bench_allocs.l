n:100000

// Int compare, vector on left each time (exercises new "reuse alpha vec" path).
b0: bench (10;"{[] ((((!100000)<1)<1)<1)<1 }[]";1)
b1: bench (10;"{[] a:(!100000); a:a<1; a:a<1; a:a<1; a:a<1; a }[]";1)

// Float compare: reuse/retag a float vector into int output (exercises "bytes-only" reuse).
c0: bench (10;"{[] ((((((!100000)/2.0)<0.5)<0.5)<0.5)<0.5) }[]";1)
c1: bench (10;"{[] a:(!100000)/2.0; a:a<0.5; a:a<0.5; a:a<0.5; a:a<0.5; a }[]";1)

t0: 4~#b0
t1: 4~#b1
t2: 4~#c0
t3: 4~#c1

u0: b0@2
u1: b1@2
v0: c0@2
v1: c1@2

t4: 1~(u1>u0)
t5: 1~(u1>(u0+u0))
t6: 1~(v1>v0)
t7: 1~(v1>(v0+v0))

t8: n~#(b0@1)
t9: n~#(c0@1)
tA: 3~@(b0@1)
tB: 3~@(c0@1)

t0*t1*t2*t3*t4*t5*t6*t7*t8*t9*tA*tB
