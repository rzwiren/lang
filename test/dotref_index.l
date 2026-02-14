d:{`a:{`b:{`c:5}}}
t0: 5~d.a.b.c
t1: 34~@d.a.x

d.a.b.c: 6
t2: 6~d.a.b.c

e:{}
e.x.y: 9
t3: 9~e.x.y

f.x: 1
t4: 1~f.x

t0*t1*t2*t3*t4
