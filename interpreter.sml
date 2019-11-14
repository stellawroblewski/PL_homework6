val _ = Control.Print.printDepth := 100;

datatype term = 
  VAR of string
| LAM of string * term
| APP of term * term 

fun without x nil = nil
  | without x (y::ys) = if x=y then without x ys
                               else y::(without x ys)
val freshVariableIndex = ref 0 
fun charlist_to_base nil = nil 
  | charlist_to_base (x::xs) = if x=(#"_") then nil else (x::(charlist_to_base xs) )

fun getFreshVariable v = 
    let val _ = (freshVariableIndex := (!freshVariableIndex) + 1)
    val i = (!freshVariableIndex)
    val base = implode (charlist_to_base (explode v))
    in (base ^ "_" ^ Int.toString i)
    end

fun union nil ys     = ys
  | union (x::xs) ys = x::(union xs (without x ys))

fun FV (VAR x)          = [x]
  | FV (LAM (x,t))      = without x (FV t)
  | FV (APP (t1,t2))    = union (FV t1) (FV t2)

fun isValue (VAR _)               = true
| isValue (LAM(x,t))              = if isValue t then true else false
| isValue ( APP(APP(t1,t2), t3))  = if isValue (APP(t1,t2) )andalso isValue t3 then true else false
| isValue (APP(x,t))              = if isValue t then true else false (*?*)

(*
and isListValue NIL           = true
  | isListValue (CONS(t1,t2)) = (isValue t1) andalso (isListValue t2)
  | isListValue _             = false
*)
fun subst (x,v) t = case t of
    (VAR y) => 
           if x=y then v 
                  else (VAR y)
  | (LAM (y,r)) =>
           if x=y then t
                  else let val z = getFreshVariable y in
                     ( LAM (z, subst (x,v)  (subst (y, VAR z) t)   ) ) end
  | (APP (t1,t2))   => APP (subst (x,v) t1  , subst (x,v) t2 )
 

fun reduceStep t = case t of

    (APP (LAM(x,t),s))   => subst (x,s) t 

  | (APP(APP(t1,t2), t3)) => if isValue t1 then APP(APP( t1, reduceStep t2), t3)
                                else APP(APP(reduceStep t1,  t2), t3)
  | (APP (t1,t2))        => APP(t1,reduceStep t2)

fun reducesTo t = let val t' = reduceStep t
                  in if t=t' then t' else reducesTo t'
                  end
(*
val map_t = REC("map","f",
           LAM("xs",
               IF (NULL (VAR "xs"),
                   NIL,
                   LET("h",HD (VAR "xs"),
                   LET("t",TL (VAR "xs"),
                   LET("fh",APP (VAR "f",VAR "h"),
                   LET("ft",APP (APP (VAR "map",VAR "f"),VAR "t"), 
                   CONS (VAR "fh",VAR "ft"))))))))
val range_t = REC("range","n",
           LAM("m",
               CONS (VAR "n",IF (EQUAL (VAR "n",VAR "m"),
                                 NIL,
                                 APP (APP (VAR "range", PLUS (VAR "n",NUM 1)), VAR "m")))))
val sqr_t = LAM("x",TIMES(VAR "x",VAR "x"))
val r1to5_t= APP(APP(range_t,NUM 1),NUM 5)
val test0 = APP(APP(map_t,sqr_t),r1to5_t)

val revhelp_t = REC("rh","xs_rxs",
                 IF(NULL(FST(VAR "xs_rxs")),
                   SND (VAR "xs_rxs"),
                   LET ("xs",FST(VAR "xs_rxs"),
                   LET ("rxs",SND(VAR "xs_rxs"),
                   APP(VAR "rh",PAIR(TL(VAR "xs"),CONS(HD(VAR "xs"),VAR "rxs")))))))
val reverse_t = LAM("xs",APP(VAR "revhelp",PAIR(VAR "xs",NIL)))
val test1 = LET("revhelp",revhelp_t,
            LET("reverse",reverse_t,
	    APP(VAR "reverse",r1to5_t)))

val fiblist_t = REC("fl","n",
                 IF(EQUAL(VAR "n",NUM 0),
                    CONS(NUM 0,NIL),
                    IF(EQUAL(VAR "n",NUM 1),
                       CONS(NUM 1,CONS(NUM 0,NIL)),
                       LET("fibs",APP(VAR "fl",PLUS(VAR "n",NEG(NUM(1)))),
                       CONS(PLUS(HD(VAR "fibs"),HD(TL(VAR "fibs"))),VAR "fibs")))))

val test2 = LET("fiblist",fiblist_t,
            APP(VAR "fiblist",NUM 10))
val test3 = LET("revhelp",revhelp_t,
            LET("reverse",reverse_t,
            LET("fiblist",fiblist_t,
            APP(VAR "reverse",APP(VAR "fiblist",NUM 10)))))

 
*)

