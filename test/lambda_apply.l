f:{[a;b] a+b}
t0: 5~[f apply (2;3)]

p:+
t1: 9~[p apply (4;5)]

g:{[x] [x; x+1; x+2]}
t2: 12~[g apply 10]

z:0
h:{[c] if[c; z:1; z:2; z]}
r0: h apply 0
t3: 2~r0
t4: 0~z

t0*t1*t2*t3*t4
