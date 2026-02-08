b0: bench (1000;+;1;2)
b1: bench (1000;-;5)

t0: 3~b0@1
t1: -5~b1@1
t2: 3~@ b0@0
t3: 3~@ ticks 0

t0*t1*t2*t3
