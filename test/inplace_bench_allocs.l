n:100000

// Bench with arena-0 peak allocation stats enabled (3rd arg == 1).
// In-place chain: no bindings => rc==0 enables reuse of the same vector across + operations.
b0: bench (10;"{[] 1+1+1+1+!100000 }[]";1)

// Fresh-allocation chain: store each intermediate in-scope => rc>0 disables in-place reuse.
b1: bench (10;"{[] 1+a:1+a:1+a:1+a:!100000 }[]";1)

t0: 4~#b0
t1: 4~#b1

u0: b0@2
u1: b1@2

t2: 1~u1>u0
t3: 1~u1>u0+u0

t4: n~#(b0@1)
t5: n~#(b1@1)
t6: 4~(b0@1)@0
t7: 4~(b1@1)@0

t0*t1*t2*t3*t4*t5*t6*t7
