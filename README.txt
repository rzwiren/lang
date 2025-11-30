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

