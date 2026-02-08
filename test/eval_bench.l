e0: eval "1+2"
e1: bench (10;"1+2")

t0: 3~e0
t1: 3~e1@1
t2: 3~@ e1@0

t0*t1*t2
