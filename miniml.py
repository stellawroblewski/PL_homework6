#
# CSCI 384 Fall 2019: miniml.py
#
# Solution to Homework 02.
# 
# A simple expression evaluator for the MiniML language.
#
# ------------------------------------------------------------
#
# The MiniML language is given by the (ambiguous) grammar
#
# <expn> ::= if <expn> then <expn> else <expn>
# <expn> ::= let val <name> = <expn> in <expn> end
# <expn> ::= let <func> in <expn> end
# <func> ::= fun <name> <name> = <expn> | fun <name> <name> = <expn> <funs>
# <funs> ::= and <name> <name> = <expn> | and <name> <name> = <expn> <funs>
# <expn> ::= fn <name> => <expn> | <expn> <expn>
# <expn> ::= <expn> <bopn> <expn>
# <expn> ::= <uopn> <expn>
# <atom> ::= <litv> | <name> | ( <expn> )
# <bopn> ::= andalso | orelse | < | = | + | - | * | div | mod
# <bopn> ::= not | print | fst | snd | exit
# <name> ::= x | i | count | fib | ... 
# <litv> ::= true | false | 0 | 1 | ...
#
# This program waits for an expression entered by the user,
# one whose syntax is expected to conform to this gramma.
# It parses that expression using the function `parseExpn`
# (after converting it to a stream of tokens), building an
# AST. It then evaluates that AST using the function `eval`.
# 
# If there are no errors, it reports the resulting value.
#
# Values are represented as "tagged" lists whose 0th component
# gives the type of the value, and whose remaining component(s)
# describe the value. For example, the lists
#
#      ["Bool", True]
#      ["Int", 35]
#
# represent a boolean and an integer, respectively. Function
# values are (expected to be) tagged with "Clos" and have
# the components of a closure as their value.
#
# The tags are used to do simple run-time type checkng when
# an AST is being evaluated. Errors are raised, for example,
# when an addition's sub-expressions don't yield an integer
# type. See the "Plus" case in 'eval' and its use of the
# function 'getIntValue" for illustration of this runtime
# type checking.
#
#
# ------------------------------------------------------------
#

import sys
import os
import time
import traceback

#
# ------------------------------------------------------------
#
# The Parser
#
# This is a series of mutually recursive parsing functions that
# consume the stream of tokens. Each one corresponds to some 
# LHS of a grammar production. Their parsing action roughly
# corresponds to each of the case of the RHSs of productions.
#
# Each takes the token stream as a parameter, and returns an AST
# of what they parsed. The AST is represented as nested Python
# lists, with each list headed by a label (a string) and with
# each list having a final element that's a string reporting
# the place in the source code where their parse started.
# So each AST node is a list of the form
#
#     ["Label", info1, info2, ... , infok, where]
#
# where "Label" gives the node type ("If", "Plus", "Num", etc.)
# k is the "arity" of that node's constructor, and where is 
# a string reporting the location where the parse occurred.
#
# That 'where' string can be used for reporting errors during
# "semantic" checks. (e.g. during interpretation, type-checking).
#
#

def parseExpn(tokens):
    where = tokens.report()
    # 
    # <expn> ::= let val <name> = <expn> in <expn> end
    #          | if <expn> then <expn> else <expn>
    #          | fn <name> => <expn>
    if tokens.next() == 'if':
        tokens.eat('if')
        e1 = parseExpn(tokens)
        tokens.eat('then')
        e2 = parseExpn(tokens)
        tokens.eat('else')
        e3 = parseExpn(tokens)
        return ["If",e1,e2,e3,where]
    elif tokens.next() == 'let':
        tokens.eat('let')
        if tokens.next() == 'val':
            tokens.eat('val')
            where_x = tokens.report()
            x = tokens.eatName()
            tokens.eat('=')
            r = parseExpn(tokens)
            d = ["Val",x,r,where_x]
        else:
            tokens.eat('fun')
            where_f = tokens.report()
            f = tokens.eatName()
            x = tokens.eatName()
            tokens.eat('=')
            r = parseExpn(tokens)
            d = ["Fun",f,x,r,where_f]
            while tokens.next() == 'and':
                where_and = tokens.report()
                tokens.eat('and')
                where_f = tokens.report()
                f = tokens.eatName()
                x = tokens.eatName()
                tokens.eat('=')
                r = parseExpn(tokens)
                dp = ["Fun",f,x,r,where_f]
                d = ["Funs",d,dp,where_and]
        tokens.eat('in')
        b = parseExpn(tokens)
        tokens.eat('end')
        return ["Let",d,b,where]
            
    elif tokens.next() == "fn":
        tokens.eat('fn')
        x = tokens.eatName()
        tokens.eat('=>')
        r = parseExpn(tokens)
        return ["Lam",x,r,where]
    else:
        return parseDisj(tokens)

def parseDisj(tokens):
    #
    # <disj> ::= <disj> orelse <conj> | <conj>
    #
    e = parseConj(tokens)
    while tokens.next() == 'orelse':
        where = tokens.report()
        tokens.eat('orelse')
        ep = parseConj(tokens)
        e = ["Or",e,ep,where]
    return e

def parseConj(tokens):
    #
    # <conj> ::= <conj> andalso <cmpn> | <cmpn>
    #
    e = parseCmpn(tokens)
    while tokens.next() == 'andalso':
        where = tokens.report()
        tokens.eat('andalso')
        ep = parseCmpn(tokens)
        e = ["And",e,ep,where]
    return e

def parseCmpn(tokens):
    #
    # <cmpn> ::= <addn> < <addn> | <addn> = <addn> | <addn>
    #
    e = parseAddn(tokens)
    if tokens.next() == '<':
        where = tokens.report()
        tokens.eat('<')
        ep = parseAddn(tokens)
        e = ["Less",e,ep,where]
    elif tokens.next() == '=':
        where = tokens.report()
        tokens.eat('=')
        ep = parseAddn(tokens)
        e = ["Equals",e,ep,where]
    return e

def parseAddn(tokens):
    #
    # <addn> ::= <addn> + <mult> | <addn> - <mult> | <mult>
    #
    e = parseMult(tokens)
    while tokens.next() in ['+','-']:
        where = tokens.report()
        if tokens.next() == '+':
            tokens.eat('+')
            ep = parseMult(tokens)
            e = ["Plus",e,ep,where]
        elif tokens.next() == '-':
            tokens.eat('-')
            ep = parseMult(tokens)
            e = ["Minus",e,ep,where]
    return e

def parseMult(tokens): 
    #
    # <mult> ::= <mult> * <nega> | <nega>
    #
    e = parseAppl(tokens)
    while tokens.next() in ['*','div','mod']:
        where = tokens.report()
        if tokens.next() == '*':
            tokens.eat('*')
            ep = parseAppl(tokens)
            e = ["Times",e,ep,where]
        elif tokens.next() == 'div':
            tokens.eat('div')
            ep = parseAppl(tokens)
            e = ["Div",e,ep,where]
        elif tokens.next() == 'mod':
            tokens.eat('mod')
            ep = parseAppl(tokens)
            e = ["Mod",e,ep,where]
    return e

BINOPS = ['andalso','orelse','<','=','+','-','*','div','mod']
STOPPERS = BINOPS + ['then', 'else', 'in', 'and', 'end', ')', ';', ',','eof']

def parseAppl(tokens): 
    #
    # <appl> ::= <appl> <nega> | <nega>
    #
    e = parsePrfx(tokens)
    while tokens.next() not in STOPPERS:
        where = tokens.report()
        ep = parsePrfx(tokens)
        e = ["App",e,ep,where]
    return e

def parsePrfx(tokens): 
    #
    # <atom> ::= not <atom> | print <atom> | <atom>
    #          | fst <atom> | snd <atom> | exit <atom>
    #
    if tokens.next() == 'not':
        where = tokens.report()
        tokens.eat('not')
        e = parseAtom(tokens)
        return ["Not",e,where]
    if tokens.next() == 'exit':
        where = tokens.report()
        tokens.eat('exit')
        e = parseAtom(tokens)
        return ["Exit",e,where]
    elif tokens.next() == 'print':
        where = tokens.report()
        tokens.eat('print')
        e = parseAtom(tokens)
        return ["Print",e,where]
    elif tokens.next() == 'fst':
        where = tokens.report()
        tokens.eat('fst')
        e = parseAtom(tokens)
        return ["First",e,where]
    elif tokens.next() == 'snd':
        where = tokens.report()
        tokens.eat('snd')
        e = parseAtom(tokens)
        return ["Second",e,where]
    else:
        return parseAtom(tokens)

def parseAtom(tokens):
    #
    # <atom> ::= 375
    #
    if tokens.nextIsInt():
        where = tokens.report()
        n = tokens.eatInt()
        return ["Literal",["Int",n],where]

    #
    # <atom> ::= () | ( <expn> )
    #          | ( <expn> ; ... ; <expn> )
    #          | ( <expn> , <expn> )
    #
    elif tokens.next() == '(':
        tokens.eat('(')
        # Unit literal
        if tokens.next() == ')':
            where = tokens.report()
            e = ["Literal",["Unit"],where]
        else:
            e = parseExpn(tokens)
            # Pairing up
            if tokens.next() == ',':
                where = tokens.report()
                tokens.eat(',')
                ep = parseExpn(tokens)
                e = ["PairUp",e,ep,where]
            else:
                # Sequencing
                while tokens.next() == ';':
                    where = tokens.report()
                    tokens.eat(';')
                    ep = parseExpn(tokens)
                    e = ["Seq",e,ep,where]
        tokens.eat(')')
        return e

    #
    # <atom> ::= <name>
    #
    elif tokens.nextIsName():
        where = tokens.report()
        x = tokens.eatName()
        return ["Var",x,where]

    #
    # <atom> ::= true
    #
    elif tokens.next() == 'true':
        where = tokens.report()
        tokens.eat('true')
        return ["Literal",["Bool",True],where]

    #
    # <atom> ::= false
    #
    elif tokens.next() == 'false':
        where = tokens.report()
        tokens.eat('false')
        return ["Literal",["Bool",False],where]

    #
    else:
        where = tokens.report()
        err1 = "Unexpected token at "+where+". "
        err2 = "Saw: '"+tokens.next()+"'. "
        raise SyntaxError(err1 + err2)

#
# ------------------------------------------------------------
#
# The Interpreter
#
def lookUpVar(x,env,err):
    for (y,v) in env:
        if y == x:
            return v
    raise RunTimeError("Use of variable '"+x+"'. "+err)


def getIntValue(taggedValue,errMsg):
    if not isinstance(taggedValue,list) or taggedValue[0] != "Int":
        raise TypeError(errMsg)
    return taggedValue[1]

def getBoolValue(taggedValue,errMsg):
    if not isinstance(taggedValue,list) or taggedValue[0] != "Bool":
        raise TypeError(errMsg)
    return taggedValue[1]

def getClosValue(taggedValue,errMsg):
    if not isinstance(taggedValue,list) or taggedValue[0] != "Clos":
        raise TypeError(errMsg)
    return taggedValue[1],taggedValue[2],taggedValue[3]

#
# def eval(env, ast):
#
#   Evaluates a MiniML expression, represented as an AST, within
#   a name-value binding environment.
#
#   Returns the resulting value.
#
def eval(env, ast):

    # Grab the AST's label and then reason about
    # each AST node by its case.
    #
    label = ast[0]

    #
    # E |- e1 V true  E |- e2 V v
    # ---------------------------
    #    E |- if(e1,e2,e3) V v
    #
    if label == 'If':
        e1 = ast[1]
        e2 = ast[2]
        e3 = ast[3]
        where = ast[-1]
        v1 = eval(env,e1)
        err = "Type error in condition at "+where+". Expected a boolean value."
        if getBoolValue(v1,err):
            return eval(env,e2)
        else:
            return eval(env,e3)

    # "let val ..." or "let fun ... " or "let fun ... and..." 
    # 
    elif label == 'Let':
        d = ast[1]
        b = ast[2]
    #
    # E |- d V u  [x -> u].E |- b V v
    # --------------------------------
    #       E |- let(val(x,r),b) V v
    #
        if d[0] == "Val":
            x = d[1]
            r = d[2]
            u = eval(env,r)
            envp = [(x,u)]+env
    #
    #         Ep |- b V v
    # -------------------------- where Ep := [f->c].E
    # E |- let(fun(f,x,r),b) V v    and c := (x |-> r; Ep)_
    #
    #
    #
    # E |- d V u     Ep |- b V v
    # ----------------------------------------------------- where Ep := [f1->c1...fk->ck].E
    # E |- let(funs(fun(f1,x1,r1),...,fun(fk,xk,rk)),b) V v   and each ci := (xi |-> ri; Ep)_
    #
        elif d[0] == "Fun" or d[0] == "Funs":
            envp = recBindAll(env,d) # handles both Fun and Funs


        return eval(envp,b)

    #
    # 
    # ------------------------------
    # E |- fn(x,r) V (x |-> r; E)_cl
    #
    elif label == 'Lam':
        x = ast[1]
        r = ast[2]
        return ["Clos",x,r,env]

    #
    # E |- e1 V (x |-> r; C)_  E |- e2 V v2  [x -> v2].C |- r V v
    # -----------------------------------------------------------
    #                     E |- app(e1,e2) V v
    #
    elif label == 'App':
        e1 = ast[1]
        e2 = ast[2]
        v1 = eval(env,e1)
        where = ast[-1]
        err = "Type error in function application at "+where+". Expected a function value."
        x,r,ctx = getClosValue(v1, err)
        v2 = eval(env,e2)
        return eval([(x,v2)]+ctx,r)

    #
    #      x in E
    # ------------------
    # E |- var(x) V E(x)
    #
    elif label == 'Var':
        x = ast[1]
        where = ast[-1]
        err = "Unbound variable at "+where+". "
        return lookUpVar(x,env,err)

    #
    # -------------------
    # E |- literal(v) V v
    #
    elif label == 'Literal':
        return ast[1]

    #
    #      E |- e1 V T
    # ----------------------
    # E |- orelse(e1,e2) V T
    #
    # E |- e1 V F    E |- e2 V b 
    # --------------------------
    #   E |- orelse(e1,e2) V b
    #
    elif label == 'Or':
        e1 = ast[1]
        e2 = ast[2]
        where = ast[-1]
        err = "Expected a boolean on the %s side of orelse at "+where+". "
        v1 = getBoolValue(eval(env,e1),err % "left")
        if v1:
            return ["Bool",True]
        else:
            v2 = getBoolValue(eval(env,e2),err % "right")
            return ["Bool",v2]

    #
    #      E |- e1 V F
    # ----------------------
    # E |- andalso(e1,e2) V F
    #
    # E |- e1 V T    E |- e2 V b 
    # ---------------------------
    #   E |- andalso(e1,e2) V b
    #
    elif label == 'And':
        e1 = ast[1]
        e2 = ast[2]
        where = ast[-1]
        err = "Expected a boolean on the %s side of andalso at "+where+". "
        v1 = getBoolValue(eval(env,e1),err % "left")
        if not v1:
            return ["Bool",False]
        else:
            v2 = getBoolValue(eval(env,e2),err % "right")
            return ["Bool",v2]

    #
    # E |- e1 V v1     E |- e2 V v2
    # ----------------------------- for op corresponding to intop
    #  E |- intop(e1,e2) V v1 op v2
    #
    elif label in INTOPS:
        e1 = ast[1]
        e2 = ast[2]
        where = ast[-1]
        err = "Expected an integer on the %s side of "+label+" at "+where+". "
        v1 = getIntValue(eval(env,e1),err % "left")
        v2 = getIntValue(eval(env,e2),err % "right")
        return ["Int",INTOPS[label](v1,v2,where)]

    #
    # E |- e1 V v1    E |- e2 V v2
    # ----------------------------  for v1 < v2
    #    E |- less(e1,e2) V T
    #
    # E |- e1 V v1    E |- e2 V v2
    # ----------------------------  for v1 >= v2
    #    E |- less(e1,e2) V F
    #
    elif label == "Less":
        e1 = ast[1]
        e2 = ast[2]
        where = ast[-1]
        err = "Expected an integer on the %s side of less at "+where+". "
        v1 = getIntValue(eval(env,e1),err % "left")
        v2 = getIntValue(eval(env,e2),err % "right")
        return ["Bool",v1 < v2]

    elif label == "Equals":
        e1 = ast[1]
        e2 = ast[2]
        where = ast[-1]
        tv1 = eval(env,e1)
        tv2 = eval(env,e2)
        if tv1[0] == 'Clos':
            raise RuntimeError("Comparing a function value at "+where+".")
        if tv2[0] == 'Clos':
            raise RuntimeError("Comparing a function value at "+where+".")
        return ["Bool",tv1 == tv2]

    #
    # E |- e1 V v1    E |- e1 V v1
    # ----------------------------
    # E |- pairup(e1,e2) V (v1,v2)
    #
    elif label == "PairUp":
        e1 = ast[1]
        e2 = ast[2]
        v1 = eval(env,e1)
        v2 = eval(env,e2)
        return ["Pair",v1,v2]

    #
    #  E |- e V (v1,v2)
    # ------------------
    # E |- first(e) V v1
    #
    elif label == "First":
        e = ast[1]
        v = eval(env,e)
        if v[0] != "Pair":
            raise RunTimeError("Attempt to extract 1st component of a non-pair at "+ast[-1]+".")
        else:
            return v[1]

    #
    #   E |- e V (v1,v2)
    # -------------------
    # E |- second(e) V v2
    #
    elif label == "Second":
        e = ast[1]
        v = eval(env,e)
        if v[0] != "Pair":
            raise RunTimeError("Attempt to extract 2nd component of a non-pair at "+ast[-1]+".")
        else:
            return v[2]

    #
    # E |- e1 V v1   E |- e2 V v2
    # ---------------------------
    #    E |- seq(e1,e2) V v2
    #
    elif label == "Seq":
        e1 = ast[1]
        e2 = ast[2]
        v1 = eval(env,e1) # We're going to toss oout this value, 
                          # but we need to evaluate its expression.
        v2 = eval(env,e2)
        return v2

    #
    #   E |- e V v
    # ------------------
    # E |- print(e) V ()
    #
    elif label == "Print":
        e = ast[1]
        tv = eval(env,e)                # Get the expression's value.
        r,t = reprTypeOfTaggedValue(tv) # Get its representation as a string.
        print(r)
        return ["Unit"]                 # The print expression yields no meaningful value.

    #
    #  
    # ------------------
    # E |- exit() V _|_
    #
    elif label == "Exit":
        sys.exit()

    #
    #   E |- e V T         E |- e V F
    # ---------------    ---------------
    # E |- not(e) V F    E |- not(e) V T
    #
    elif label == "Not":
        e = ast[1]
        where = ast[-1]
        v = getBoolValue(eval(env,e), "Expected a boolean for logical negation at "+where+".")
        return ["Bool",not v]

    else:
        return ["Bottom"]
    
def checkDiv0(divisor, where):
    if divisor == 0:
        raise RunTimeError("Attempt to divide by zero at "+where+".")
    return divisor
        
    
INTOPS = {"Plus": (lambda iv1,iv2,w: iv1+iv2),
          "Minus": (lambda iv1,iv2,w: iv1-iv2),
          "Times": (lambda iv1,iv2,w: iv1*iv2),
          "Div": (lambda iv1,iv2,w: iv1 // checkDiv0(iv2,w)),
          "Mod": (lambda iv1,iv2,w: iv1 % iv2)}
CMPOPS = {"Equals": (lambda iv1,iv2,w: iv1 == iv2), 
          "Less": (lambda iv1,iv2,w: iv1 < iv2)}

# 
# closureBinding(d):
#
#   Given d == ["Fun", f, x, r], this builds and returns a named
#   closure, missing its captured context, as a name-value binding.
#
def closureBinding(d):
    f = d[1]
    x = d[2]
    r = d[3]
    fv = ["Clos",x,r,None]
    return (f,fv)

# 
# recBindAll(env, ds):
#
#   Given ds == ["Funs", ... ] or ds == ["Fun", ... ]
#   that is, function definition(s) that are part of a let, 
#   build a list [(f1,c1), ... , (fk,ck)] of function-closure
#   bindings for their mutually recursive definition, and
#   extend the given env with them, returning a new
#   environment.
#

def recBindAll(env, ds):

    # Step 1: Unpack the "let fun (...and...)" AST and build a collection of closures.
    # Step 2: Tie the loop for each closure, making it recursive.
    # Step 3: Give back an extended environment with each of them bound. 

    fvs = []   # The list of closures that we form in Step 1 and fix in Step 2.
    envp = env # The environment we want to return in Step 3.
    
    # Step 1.
    # Build a collection of function closures, and extend the
    # environment to have their names bound to them. Each 
    # closure will be missing its captured context. We'll
    # fix that in Step 2. This gives us a collection of 
    # mutually recursive closures. We write this as a loop 
    # below. 
    #
    # Note that the code is more naturally recursive, except
    # we need to do the "fix the broken closures" Step 2
    # afterwards. So instead we handle the base case within 
    # the loop's body. This, btw, happens to handle the case
    # when there is only a single recursive function.
    #
    while ds is not None:
        # Unpack structure
        #          Funs
        #           / \
        #       Funs   Fun
        #        / \   ...
        #     ...   Fun  
        #     /     ...
        #  Funs
        #   / \
        # Fun  Fun
        # ...  ...
        # and make a list of bindings of closures.
        if ds[0] == "Funs":
            # We're not at the last.
            d = ds[2]    # Get the function definition.
            ds = ds[1]   # Prepare for the next iteration.
        else: 
            # It's at the bottom, just a Fun
            d = ds       # At the bottom, it *is* the last definition
            ds = None    # Indicate that we're done for the next iteration.
            
        f,fv = closureBinding(d)
        fvs = [fv] + fvs        # Make a list of closures to fix in Step 2.
        envp = [(f,fv)] + envp  # Make an environment to return in Step 3.
    #
    # Step 2.
    # Fix all the broken closures so that each function knows about
    # itself and the others.
    #
    for fv in fvs:
        fv[3] = envp

    # Step 3.
    # Give back that extended environbment.
    return envp


#
# ------------------------------------------------------------
#

#
# Exceptions
#
# These define the exception raised by the interpreter.
#
class TypeError(Exception):
    pass

class RunTimeError(Exception):
    pass

class ParseError(Exception):
    pass

class SyntaxError(Exception):
    pass

class LexError(Exception):
    pass

# 
# Keywords, primitives, unary operations, and binary operations.
#
# The code below defines several strings or string lists used by
# the lexical analyzer (housed as class TokenStream, below).
#

RESERVED = ['if','then','else',
            'let', 'val', 'fun', 'and', 'in', 'end',
            'fn',
            'orelse','andalso',
            'div','mod',
            'true','false',
            'print',
            'fst','snd',
            'eof']

# Characters that separate expressions.
DELIMITERS = '();,|'

# Characters that make up unary and binary operations.
OPERATORS = '+-*/<>=&!:.' 


#
# LEXICAL ANALYSIS / TOKENIZER
#
# The code below converts ML source code text into a sequence 
# of tokens (a list of strings).  It does so by defining the
#
#    class TokenStream
#
# which describes the methods of an object that supports this
# lexical conversion.  The key method is "analyze" which provides
# the conversion.  It is the lexical analyzer for ML source code.
#
# The lexical analyzer works by CHOMP methods that processes the
# individual characters of the source code's string, packaging
# them into a list of token strings.
#
# The class also provides a series of methods that can be used
# to consume (or EAT) the tokens of the token stream.  These are
# used by the parser.
#


class TokenStream:

    def __init__(self,src,filename="STDIN"):
        """
        Builds a new TokenStream object from a source code string.
        """
        self.sourcename = filename
        self.source = src # The char sequence that gets 'chomped' by the lexical analyzer.
        self.tokens = []  # The list of tokens constructed by the lexical analyzer.
        self.extents = []     
        self.starts = []

        # Sets up and then runs the lexical analyzer.
        self.initIssue()
        self.analyze()
        self.tokens.append("eof")

    #
    # PARSING helper functions
    #

    def lexassert(self,c):
        if not c:
            self.raiseLex("Unrecognized character.")

    def raiseLex(self,msg):
        s = self.sourcename + " line "+str(self.line)+" column "+str(self.column)
        s += ": " + msg
        raise LexError(s)

    def next(self):
        """
        Returns the unchomped token at the front of the stream of tokens.
        """
        return self.tokens[0]

    def advance(self):
        """ 
        Advances the token stream to the next token, giving back the
        one at the front.
        """
        tk = self.next()
        del self.tokens[0]
        del self.starts[0]
        return tk

    def report(self):
        """ 
        Helper function used to report the location of errors in the 
        source code.
        """
        lnum = self.starts[0][0]
        cnum = self.starts[0][1]
        return self.sourcename + " line "+str(lnum)+" column "+str(cnum)

    def eat(self,tk):
        """
        Eats a specified token, making sure that it is the next token
        in the stream.
        """
        if tk == self.next():
            return self.advance()
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected: '"+tk+"'. "
            raise SyntaxError(err1 + err2 + err3)

    def eatInt(self):
        """
        Eats an integer literal token, making sure that such a token is next
        in the stream.
        """
        if self.nextIsInt():
            tk = self.advance()
            if tk[0] == '-':
                return -int(tk[1:])
            else:
                return int(tk)
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected an integer literal. "
            raise SyntaxError(err1 + err2 + err3)

    def eatName(self):
        """
        Eats a name token, making sure that such a token is next in the stream.
        """
        if self.nextIsName():
            return self.advance()
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected a name. "
            raise SyntaxError(err1 + err2 + err3)

    def eatString(self):
        """
        Eats a string literal token, making sure that such a token is next in the stream.
        """
        if self.nextIsString():
            return self.advance()[1:-1]
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected a string literal. "
            raise SyntaxError(err1 + err2 + err3)

    def nextIsInt(self):
        """
        Checks if next token is an integer literal token.
        """
        tk = self.next()
        return tk.isdigit()

    def checkEOF(self):
        """
        Checks if next token is an integer literal token.
        """
        if self.next() != 'eof':
            raise ParseError("Parsing failed to consume tokens "+str(self.tokens[:-1])+".")


    def nextIsName(self):
        """
        Checks if next token is a name.
        """
        tk = self.next()
        isname = tk[0].isalpha() or tk[0] =='_'
        for c in tk[1:]:
            isname = isname and (c.isalnum() or c == '_')
        return isname and (tk not in RESERVED)

    def nextIsString(self):
        """
        Checks if next token is a string literal.
        """
        tk = self.next()
        return tk[0] == '"' and tk[-1] == '"'

    #
    # TOKENIZER helper functions
    #
    # These are used by the 'analysis' method defined below them.
    #
    # The parsing functions EAT the token stream, whereas
    # the lexcial analysis functions CHOMP the source text
    # and ISSUE the individual tokens that form the stream.
    #

    def initIssue(self):
        self.line = 1
        self.column = 1
        self.markIssue()

    def markIssue(self):
        self.mark = (self.line,self.column)

    def issue(self,token):
        self.tokens.append(token)
        self.starts.append(self.mark)
        self.markIssue()

    def nxt(self,lookahead=1):
        if len(self.source) == 0:
            return ''
        else:
            return self.source[lookahead-1]

    def chompSelector(self):
        self.lexassert(self.nxt() == '#' and self.nxt(2).isdigit())
        token = self.chompChar()
        token = '#'
        while self.nxt().isdigit():
            token += self.chompChar()
        self.issue(token)

    def chompWord(self):
        self.lexassert(self.nxt().isalpha() or self.nxt() == '_')
        token = self.chompChar()
        while self.nxt().isalnum() or self.nxt() == '_':
            token += self.chompChar()
        self.issue(token)
        
    def chompInt(self):
        ck = self.nxt().isdigit()
        self.lexassert(ck)
        token = ""
        token += self.chompChar()     # first digit
        while self.nxt().isdigit():
            token += self.chompChar() # remaining digits=
        self.issue(token)
        
    def chompString(self):
        self.lexassert(self.nxt() == '"')
        self.chompChar() # eat quote
        token = ""
        while self.nxt() != '' and self.nxt() != '"':
            if self.nxt() == '\\':
                self.chompChar()
                if self.nxt() == '\n':
                    self.chompWhitespace(True)
                elif self.nxt() == '\\':
                    token += self.chompChar()
                elif self.nxt() == 'n':
                    self.chompChar()
                    token += '\n'
                elif self.nxt() == 't':
                    self.chompChar()
                    token += '\t'
                elif self.nxt() == '"': 
                    self.chompChar()
                    token += '"'
                else:
                    self.raiseLex("Bad string escape character")
            elif self.nxt() == '\n':
                self.raiseLex("End of line encountered within string")
            elif self.nxt() == '\t':
                self.raiseLex("Tab encountered within string")
            else:
                token += self.chompChar()

        if self.nxt() == '':
            self.raiseLex("EOF encountered within string")
        else:
            self.chompChar() # eat endquote
            self.issue('"'+token+'"')

    def chompComment(self):
        self.lexassert(len(self.source)>1 and self.source[0:2] == '(*')
        self.chompChar() # eat (*
        self.chompChar() #
        while len(self.source) >= 2 and self.source[0:2] != '*)':        
            self.chomp()
        if len(self.source) < 2:
            self.raiseLex("EOF encountered within comment")
        else:
            self.chompChar() # eat *)
            self.chompChar() #     

    def chomp(self):
        if self.nxt() in "\n\t\r ":
            self.chompWhitespace()
        else:
            self.chompChar()

    def chompChar(self):
        self.lexassert(len(self.source) > 0)
        c = self.source[0]
        self.source = self.source[1:]
        self.column += 1
        return c

    def chompWhitespace(self,withinToken=False):
        self.lexassert(len(self.source) > 0)
        c = self.source[0]
        self.source = self.source[1:]
        if c == ' ':
            self.column += 1
        elif c == '\t':
            self.column += 4
        elif c == '\n':
            self.line += 1
            self.column = 1
        if not withinToken:
            self.markIssue()
        
    def chompOperator(self):
        token = ''
        while self.nxt() in OPERATORS:
            token += self.chompChar()
        self.issue(token)

    #
    # TOKENIZER
    #
    # This method defines the main loop of the
    # lexical analysis algorithm, one that converts
    # the source text into a list of token strings.

    def analyze(self):
        while self.source != '':
            # CHOMP a string literal
            if self.source[0] == '"':
                self.chompString()
            # CHOMP a comment
            elif self.source[0:2] == '(*':
                self.chompComment()
            # CHOMP whitespace
            elif self.source[0] in ' \t\n\r':
                self.chompWhitespace()
            # CHOMP an integer literal
            elif self.source[0].isdigit():
                self.chompInt()
            # CHOMP a single "delimiter" character
            elif self.source[0] in DELIMITERS:
                self.issue(self.chompChar())
            # CHOMP an operator               
            elif self.source[0] in OPERATORS:
                self.chompOperator()
            # CHOMP a reserved word or a name.
            else:
                self.chompWord()


def reprTypeOfTaggedValue(taggedValue):
    if isinstance(taggedValue,list) or len(taggedValue) < 2:
        tag = taggedValue[0]
        if tag == "Unit":
            return ("()",'unit')
        elif tag == "Int":
            val = taggedValue[1]
            return (repr(val),'int')
        elif tag == "Bool":
            val = taggedValue[1]
            return (repr(val).lower(),'bool')
        elif tag == "Clos":
            return ('fn','fn')
        elif tag == "Pair":
            v1 = taggedValue[1]
            v2 = taggedValue[2]
            r1,t1 = reprTypeOfTaggedValue(v1)
            r2,t2 = reprTypeOfTaggedValue(v2)
            return ('('+r1+','+r2+')','('+t1+ '*' +t2+')')
        elif tag == "Bottom":
            return ('_|_','error')
    raise RunTimeError("Interpreter incorrectly constructed a bad value.")

def interpret(tks, expect_semi = False):
    ast = parseExpn(tks)                   # Parse the entry.
    if expect_semi:
        tks.eat(";")
    tks.checkEOF()                         # Check if everything was consumed by the parse
    tval = eval([],ast)                    # Evaluate the entry in an empty context.
    val,typ = reprTypeOfTaggedValue(tval)  # Report the resulting value.
    print("val it =",val,":",typ)

def evalAll(files):
    try:
        # Load definitions from the specified source files.
        for fname in files:
            print("[opening "+fname+"]")
            f = open(fname,"r")
            src = f.read()
            tks = TokenStream(src,filename=fname)
            interpret(tks)
    except RunTimeError as e:
        print("Error during evaluation.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except RunTimeError as e:
        print("Type error during evaluation.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except SyntaxError as e:
        print("Syntax error during parse.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except ParseError as e:
        print("Failed to consume all the input in the parse.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except LexError as e:
        print("Bad token reached.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except Exception:
        print("Unexpected error.")
        traceback.print_exc()
        print("Bailing command-line loading.")
        
#
#  usage #1: 
#    python3 miniml.py
#
#      - Waits for a MiniML expression after the prompt
#        evaluates it, and prints the resulting value
#
#
#  usage #2: 
#    python3 miniml.py <file 1> ... <file n>
#
#      - this runs the interpreter on each of the listed
#        source .mml files
#
mtime = str(time.ctime(os.path.getmtime("./miniml.py")))
print("MiniML of Portlandia v2019F.1 [built: "+mtime+"]")
if len(sys.argv) > 1:
    evalAll(sys.argv[1:])
else:
    while True:
        print("- ",end='')
        try: 
            line = input()
        except:
            sys.exit()
        interpret(TokenStream(line),expect_semi=True)
