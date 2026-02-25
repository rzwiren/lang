fn:"test/tmp_texttry.txt"
payload:"abc
def"

fn text payload;

r:texttry fn
t0: 1~(r@0)
t1: 1~((r@1)~payload)

r2:texttry "test/no_such_file_texttry_123.txt"
t2: 0~(r2@0)
t3: 0~#(r2@1)

r3:texttry 123
t4: 0~(r3@0)
t5: 0~#(r3@1)

t0*t1*t2*t3*t4*t5
