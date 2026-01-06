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
   no ambivalence for clarity
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
  What tradeoffs can we make in one area to benefit another and the whole system and what tradeoffs various choices introduce
  Indexing
   how does indexing into data relate to function dispatch?

This interpreter is essentially an abstract machine. It works off of a Q (quadword/64bit) register size.
 A Q has different representations based on the metadata stored in the lower bits. 
 The system assumes the smallest possible alignment is 16 byte alignment. 
  This means that any pointer type object will have 4 free low bits.
  Those 4 low bits are used to encode a type tag
   0 - pointer like object
   1 - reference
   2 - grammatical
    2 - verbs
    18 - adverbs
    34 - control (todo split out control characters for errors at runtime from grammatical objects like (){}[])
   3 - number
   4 - partial evaluation. never atom (eventually move this into grammatical?)
   5 - hash. never atom.
   6 - character
   7 - symbol
   8 - file (todo)
  the metadata in a Q is type dependent (p:payload,f:fileid,a:arenaid,o:order,t:typetag). Data is organized into arenas 0-7
   0 -
    file backed 
     2 - (read only file backed snapshot) 58p2a4t
     3 - (many small files, still needs thought) 37p16f2a5o4t
    ram backed (a in 0..6) 53p5o2a4t
     0 - (temp allocations) 58p2a4t
     1 - (global allocations) 52p5o3a4t
   1,3,7 - 60p4t
   2 - 58p2a4t (there are 2 more bits worth of subtypes for the grammatical types with low bits == 2)
the arena portion of a Q is a way for the system to find the base address used to calculate the true pointer to that Q
the payload part of the Q constitutes the offset. 
 The offset is stored in units of the minimum allocation granularity for that arenas allocator
 e.g. if the min allocation granularity is 2^12 then the offset 0+base is pointing at a range of 2^12 bytes.
 allocators will respect alignment based on the minimum allocation granularity which is at least 16 bytes. 
the order portion of pointer like Q objects is 5 bits because 
 31 distinct monotonically increasing allocation sizes should be sufficient regardless of the allocator backing the arena.
 temp arena (bump allocated)
  smallest size of allocation is 16 bytes, 
  largest is 8 bytes*2^32 (what if we add support for 128bit uuids?)
  needs 
 global arena (buddy)
  min size 2^12 bytes (page)
  max size 8*2^32 bytes
 the largest vector size is currently 2^32 
 and the minimum allocation size is 16 bytes 
 so any allocator implementation needs 5 bits to represent all possible allocation sizes. 
  it is worth noting that some allocators don't pay attention to those 5 bits (bump, filebump) so they do not need to be stored
   this allows for larger payloads for those allocators. 

vb is already a tool that can be used to do a depth first walk. you can reimplement t2g and printing to use vb like any other verb. write a copying verb and then arena to arena copyign become parameterizations.

Guiding Principles of Design:
 1. Embrace the fact that a CPU is an interpreter
 2. Hardware engineers are brilliant. Use/expose the wonderful tools they have given to us.
  a. Three dimensions are enough (length x element width x lanecount). No need to optimize for multi dimensional arrays.
  a. Expose SIMD cleanly. Don't try to stuff vector tools through scalar APIs that we call programming languages. 