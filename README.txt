Lang. 
 A case study in array programming language interpreter topology.
 Richard P. Zwiren Jr.

Why am I doing this?
 From the days that I first starting using q I often wondered how the interpreter worked under the hood. 
Areas explored: 
 Lexical Analysis
 Grammar
  simple infix evaluator
   text files are two dimensional data structures, but code and the written word is truly one dimensional (why we need parens)
   sentences/statements
   phrases/expressions
   grammatical robustness to missing arguments. two cases:
    + (dyad missing both args)
    1+(dyad missing right arg)
  noun
  verb
  adverb
 Operator dispatch
  verbs
   ambivalence
   atomic
   uniform
  adverbs
 Demonstrate techniques to efficiently organize data
  Data types
   pointer
   reference
   function
   integer
   floating point
  Data widths
   1 2 4 8 byte width support
  Data shapes
   scalar
   vector
   tree
    general list
    dictionary
    table
 Demonstrate techniques to efficiently allocate memory
  Pointer layout
  Allocation granularity: What is the smallest and largest allocation supported
  Address space management
  Garbage collection and reference counting
 I/O
  disk
  network
How do each of the explored areas overlap?
  What tradeoffs can we make in one area to benefit another and the whole systemand what tradeoffs various choices introduce
  Indexing
   how does indexing into data relate to function dispatch?

=======

random notes:

Can I come up with a better type 0? CONSIER A DEDICATED VERB TO CREATE THIS INSTEAD OF WITHIN MANY VERBS

current setup for shape 3 is
( 5 1 2 2 1  2  2 3 2 2 7 ; n
1 0 1 3 16 17 3 5 5 7 9 ; offset from base to first child
0 1 2 3 4 5 6 7 8  9 10 11 12 13 14 15 16 17 18) data

algorithms involving shape 3 are tedious to write... can you use simpler apis for basic pointers to implement the metadata manipulations for shape 3?                                                   

versus
p0->[a1,p2,p3,a2,p9]
p3->[p4,p5]
p5->[p6,p7,p8]

which is 10 pointers x 8 bytes/pointer = 80 bytes

Memory allocation factors for consideration: 
A range of low bits in a pointer can be guaranteed to be 0 by changing the smallest allocation size. 
byte aligned is multiple of 8   000
w    aligned                16  0000
d                           32  00000
q                           64  000000
o                           128 0000000
h                           256 00000000
i                           512 000000000

and so on.
Address space is plentiful. even with 512 byte alignment we have room for 2^39~=549 billion allocations.
That's far more than any practical workload would need. 
That makes me want to do saves to disk with nearly raw memory dumps. Run length encoding would compress awesomely. 
a smaller alignment would allow for mapping in place without blowing out disk too much though... 

if I go with 512 byte alignment then I have a 16 39 9 pointer setup
this gives me 25 bits to play with
I use 8 for type width and shape already
17 free bits for other purposes. 
so that means monadic verbs get 17 free bits
and dyadic verbs get 34 free bits
what can I use the free bits for?
I can encode in a single bit whether an argument can be reused without reallocating a new object
I can encode the verb in some other bits. this might be useful in order to save space during dispatch
I can also carry a refcount around. 16 bit refcounts will definitely overflow though. 

