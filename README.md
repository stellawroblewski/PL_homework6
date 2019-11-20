# Homework 06: a lambda calculus reduction engine
### Reed CSCI 384 Fall 2019
### Stella Wroblewski and David Tamas-Parris
---

## ASSIGNMENT

**Part 1. The parser.**  
Written in python, making tweaks to the solution for homework 3. The syntax for parsing is similar to that used in class, with a semicolon after each named lambda term. 

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
(NOTE: some of the more complication lambda functions, like fib and collatz, take a decently long time to fully run. Even simple functions like is_even take at least a minute on small inputs like three.)

Even though the reduction engine is written in sml, the evaluation of a .lc program is done by the python program. Running a .lc program would happen like this:

`python lambda_engine.py my_program.lc`

The python program creates a large lambda calculus term for evaluation, prints it into a tmp.sml file, and runs the .sml file using the `sys` package.

**Part 4. testing**  
Our tests beyond the required lambda calculus functions include a '.lc' files containing a recursive power function, recursive and iterative factorial, is_even, division, and a collatz function. The collatz function does not finish running on the input of 4, ending in an overflow error. We are unsure if this is an error in the lambda calculus implemention, or a result of inefficient interpretation.

**Part 5. write some terms**  
For each of the required functions there is a simple test implementing them within their named '.lc' files inside of the 'main' function. The implementations of `pred` and `power` were taken from Wikipedia, so we feel the need to at least explain their mechanics here.

`pred` relies on a helper term `phi` that maps a pair (m,n) to (n,n+1):

`pred := fn n => first ( n phi (pair zero zero ))`

n applications of phi to (0,0) results in the pair (n-1,n) if n>0 and simply (0,0) if n=0, so taking the first element of this pair suffices for finding the predicate.

We have 

`power := fn m => fn n => n m`

This reduces to

(fn f => fn x => f( f (.... f  x)...)  ) m

~~~> fn x=> m ( m ( m (...m x )    ) ),

with m repeated n times. Using the same reasoning used to derive times, this will reduce to:

fn x => fn x' => x ( x ( x (... x x'     ))),

with x repeated m^n times. 


Additionally, for several of the functions, there are numbered files running various tests on the same function. 







