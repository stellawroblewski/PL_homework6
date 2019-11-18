# Homework 06: a lambda calculus reduction engine
### Reed CSCI 384 Fall 2019

---

## ASSIGNMENT

**Part 1. The parser.**  
Written in python. 
**Part 2. The term.**  
Having parsed these files, you should produce a single lambda caclulus
term that is to be reduced. This will, of course, require you to
carefully substitute the definitions of names of terms into the term
The parser takes in files like this `sample2.lc`:

    zz := fn f => fn x => x; 
    zf := fn y => zz;
    main := zf zz;

and reduces a term like this:

    APP(LAM("zz",APP(LAM("zf",APP(VAR "zf",VAR "zz")),LAM("y",VAR "zz")),LAM("f",LAM("x",VAR "x")))

**Part 3. reduction**  
Written in SML. 
(NOTE: some of the more complication lambda functions, like fib and collatz, take a decently long time to fully run.)

**Part 4. testing**  
Our tests beyond the required lambda calculus functions include a '.lc' files containing a recursive power function, recursive and iterative factorial, is_even, division, and a collatz function.

**Part 5. write some terms**  
For each of the required functions there is a simple test implementing them within their named '.lc' files inside of the 'main' function. Additionally, for several of the functions, there are numbered files running various tests on the same function. 







