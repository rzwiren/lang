fn:"test/tmp_text_io.txt"
payload:"line1
line2
line3"

empty:""
fn2:"test/tmp_text_io_empty.txt"

fn text payload;
fn2 text empty;

r:text fn;
r2:text fn2;

t0: 1~(payload~r)
t1: 1~(empty~r2)

t0*t1
