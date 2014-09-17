(* upr.sml 559a *)


(*****************************************************************)
(*                                                               *)
(*   ENVIRONMENTS                                                *)
(*                                                               *)
(*****************************************************************)

(* environments 214 *)
type name = string
type 'a env = (name * 'a) list
val emptyEnv = []

(* lookup and assignment of existing bindings *)
exception NotFound of name
fun find (name, []) = raise NotFound name
  | find (name, (n, v)::tail) = if name = n then v else find (name, tail)

(* adding new bindings *)
exception BindListLength
fun bind (name, v, rho) = (name, v) :: rho
fun bindList (n::vars, v::vals, rho) = bindList (vars, vals, bind (n, v, rho))
  | bindList ([], [], rho) = rho
  | bindList _ = raise BindListLength
(* type declarations for consistency checking *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* environments 720c *)
val tracer = ref (app print)
val _ = tracer := (fn _ => ())
fun trace l = !tracer l


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values ((upr)) 529a *)
datatype term = VAR     of string
              | LITERAL of int
              | APPLY   of string * term list
(* abstract syntax and values ((upr)) 529b *)
type goal = string * term list
(* abstract syntax and values ((upr)) 529c *)
datatype clause = :- of goal * goal list
infix 3 :-
(* abstract syntax and values ((upr)) 530 *)
datatype cq
  = ADD_CLAUSE of clause
  | QUERY      of goal list
  | USE        of string
(* abstract syntax and values ((upr)) 551a *)
(* string conversions ((upr)) 709 *)
fun termString (APPLY ("cons", [car, cdr])) = 
      let fun tail (APPLY ("cons", [car, cdr])) = ", " ^ termString car ^ tail
                                                                             cdr
            | tail (APPLY ("nil",  []))         = "]"
            | tail x                           = "|" ^ termString x ^ "]"
      in  "[" ^ termString car ^ tail cdr
      end
  | termString (APPLY ("nil", [])) = "[]"
  | termString (APPLY (f, []))     = f
  | termString (APPLY (f, [x, y])) =
      if Char.isAlpha (hd (explode f)) then appString f x [y]
      else String.concat ["(", termString x, " ", f, " ", termString y, ")"]
  | termString (APPLY (f, h::t)) = appString f h t
  | termString (VAR v) = v
  | termString (LITERAL n) = String.map (fn #"~" => #"-" | c => c) (Int.toString
                                                                              n)
and appString f h t =
      String.concat (f :: "(" :: termString h ::
                     foldr (fn (t, tail) => ", " :: termString t :: tail) [")"]
                                                                              t)
(* string conversions ((upr)) 710a *)
fun goalString g = termString (APPLY g)
fun clauseString (g :- []) = goalString g
  | clauseString (g :- (h :: t)) =
      String.concat (goalString g :: " :- " :: goalString h ::
                     (foldr (fn (g, tail) => ", " :: goalString g :: tail)) [] t
                                                                               )
(* type declarations for consistency checking *)
val _ = op termString   : term   -> string
val _ = op goalString   : goal   -> string
val _ = op clauseString : clause -> string


(*****************************************************************)
(*                                                               *)
(*   CLAUSE DATABASE                                             *)
(*                                                               *)
(*****************************************************************)

(* clause database 551b *)
type database = clause list
val emptyDatabase = []
fun addClause (r, rs) = rs @ [r] (* must maintain order *)
fun potentialMatches (_, rs) = rs


(*****************************************************************)
(*                                                               *)
(*   SUBSTITUTION AND UNIFICATION                                *)
(*                                                               *)
(*****************************************************************)

(* substitution and unification ((upr)) 552b *)
(* substitution on terms ((prototype)) 552a *)
exception LeftAsExercise
type subst = term -> term
infix 7 |-->
fun name |--> term = raise LeftAsExercise
fun idsubst term = term
(* type declarations for consistency checking *)
type database = database
val _ = op emptyDatabase    : database
val _ = op addClause        : clause * database -> database
val _ = op potentialMatches : goal * database -> clause list
(* type declarations for consistency checking *)
type subst = subst
val _ = op idsubst : subst
val _ = op |-->    : name * term -> subst
(* substitution and unification ((upr)) 552c *)
fun lift       theta (f, l)    = (f, map theta l)
fun liftClause theta (c :- ps) = (lift theta c :- map (lift theta) ps)
(* type declarations for consistency checking *)
val _ = op lift       : subst -> (goal   -> goal)
val _ = op liftClause : subst -> (clause -> clause)
(* substitution and unification ((upr)) 552d *)
type 'a set = 'a list
val emptyset = []
fun member x = 
  List.exists (fn y => y = x)
fun insert (x, l) = 
  if member x l then l else x::l
fun diff  (s1, s2) = 
  List.filter (fn x => not (member x s2)) s1
fun union (s1, s2) = s1 @ diff (s2, s1)   (* preserves order *)
(* type declarations for consistency checking *)
type 'a set = 'a set
val _ = op emptyset : 'a set
val _ = op member   : ''a -> ''a set -> bool
val _ = op insert   : ''a     * ''a set  -> ''a set
val _ = op union    : ''a set * ''a set  -> ''a set
val _ = op diff     : ''a set * ''a set  -> ''a set
(* substitution and unification ((upr)) 553a *)
fun freevars t =
  let fun f(VAR v,     l) = insert (v, l)
        | f(LITERAL _, l) = l
        | f(APPLY(_, args), l) = foldl f l args
  in  rev (f(t, []))
  end  
fun freevarsGoal goal = freevars (APPLY goal)
fun freevarsClause (c :- ps) =
  foldl (fn (p, f) => union (freevarsGoal p, f)) (freevarsGoal c) ps
(* type declarations for consistency checking *)
val _ = op freevars       : term   -> name set
val _ = op freevarsGoal   : goal   -> name set
val _ = op freevarsClause : clause -> name set
(* substitution and unification ((upr)) 553b *)
local
  val n = ref 1
in
  fun freshVar s = VAR ("_" ^ s ^ Int.toString (!n) before n := !n + 1)
(* type declarations for consistency checking *)
val _ = op freshVar : string -> term
end
(* substitution and unification ((upr)) 553c *)
fun freshen c =
  let val free     = freevarsClause c
      val fresh    = map freshVar free
      val renaming =
        ListPair.foldl (fn (free, fresh, theta) => theta o (free |--> fresh))
        idsubst (free, fresh) 
  in  liftClause renaming c
  end
(* substitution and unification ((upr)) 554 *)
(* unification ((prototype)) 553d *)
exception Unify
fun unifyTerm (t1, t2) = 
  raise LeftAsExercise
and unifyList (ts1, ts2) = 
  raise LeftAsExercise
fun unify ((f, args), (f', args')) =
  if f = f' then unifyList (args, args') else raise Unify
(* type declarations for consistency checking *)
val _ = op freshen : clause -> clause
(* type declarations for consistency checking *)
val _ = op unify     : goal      * goal      -> subst
val _ = op unifyTerm : term      * term      -> subst
val _ = op unifyList : term list * term list -> subst


(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS                                            *)
(*                                                               *)
(*****************************************************************)

(* lexical analysis ((upr)) 710b *)
datatype token 
  = UPPER     of string
  | LOWER     of string
  | SYMBOLIC  of string
  | INT_TOKEN of int
  | RESERVED  of string
  | EOF
(* type declarations for consistency checking *)
type token = token
(* lexical analysis ((upr)) 710c *)
fun tokenString (UPPER s)     = s
  | tokenString (LOWER s)     = s
  | tokenString (INT_TOKEN n) = if n < 0 then "-" ^ Int.toString (~n)
                                else Int.toString n
  | tokenString (SYMBOLIC  s) = s
  | tokenString (RESERVED  s) = s
  | tokenString EOF           = "<end-of-file>"
(* lexical analysis ((upr)) 710d *)
fun isLiteral s t = (s = tokenString t)
(* support for streams, lexical analysis, and parsing 644 *)
(* suspensions 646 *)
datatype 'a action
  = PENDING  of unit -> 'a
  | PRODUCED of 'a

type 'a susp = 'a action ref

fun delay f = ref (PENDING f)
fun force cell =
  case !cell
    of PENDING f =>  let val result = f ()
                     in  (cell := PRODUCED result; result)
                     end
     | PRODUCED v => v
(* type declarations for consistency checking *)
val _ = op delay : (unit -> 'a) -> 'a susp
val _ = op force : 'a susp -> 'a
(* streams 647a *)
datatype 'a stream 
  = EOS
  | :::       of 'a * 'a stream
  | SUSPENDED of 'a stream susp
infixr 3 :::
(* streams 647b *)
fun streamGet EOS = NONE
  | streamGet (x ::: xs)    = SOME (x, xs)
  | streamGet (SUSPENDED s) = streamGet (force s)
(* streams 647c *)
fun streamOfList xs = 
  foldr (op :::) EOS xs
(* type declarations for consistency checking *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* type declarations for consistency checking *)
val _ = op streamOfList : 'a list -> 'a stream
(* streams 647d *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* streams 647e *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* type declarations for consistency checking *)
val _ = op listOfStream : 'a stream -> 'a list
(* type declarations for consistency checking *)
val _ = op delayedStream : (unit -> 'a stream) -> 'a stream
(* streams 648a *)
fun streamOfEffects next =
  delayedStream (fn () => case next () of NONE => EOS
                                        | SOME a => a ::: streamOfEffects next)
(* type declarations for consistency checking *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* streams 648b *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* type declarations for consistency checking *)
type line = line
val _ = op streamOfLines : TextIO.instream -> line stream
(* streams 648c *)
fun streamRepeat x =
  delayedStream (fn () => x ::: streamRepeat x)
(* type declarations for consistency checking *)
val _ = op streamRepeat : 'a -> 'a stream
(* streams 648d *)
fun streamOfUnfold next state =
  delayedStream (fn () => case next state
                            of NONE => EOS
                             | SOME (a, state) => a ::: streamOfUnfold next
                                                                          state)
(* type declarations for consistency checking *)
val _ = op streamOfUnfold : ('b -> ('a * 'b) option) -> 'b -> 'a stream
(* streams 649a *)
fun preStream (pre, xs) = 
  streamOfUnfold (fn xs => (pre (); streamGet xs)) xs
(* streams 649b *)
fun postStream (xs, post) =
  streamOfUnfold (fn xs => case streamGet xs
                             of NONE => NONE
                              | head as SOME (x, _) => (post x; head)) xs
(* type declarations for consistency checking *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* type declarations for consistency checking *)
val _ = op postStream : 'a stream * ('a -> unit) -> 'a stream
(* streams 649c *)
fun streamMap f xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => f x ::: streamMap f xs)
(* type declarations for consistency checking *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* streams 649d *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* type declarations for consistency checking *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* streams 650a *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* type declarations for consistency checking *)
val _ = op streamFold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b

(* streams 650b *)
fun streamZip (xs, ys) =
  delayedStream
  (fn () => case (streamGet xs, streamGet ys)
              of (SOME (x, xs), SOME (y, ys)) => (x, y) ::: streamZip (xs, ys)
               | _ => EOS)
(* streams 650c *)
fun streamConcat xss =
  let fun get (xs, xss) =
        case streamGet xs
          of SOME (x, xs) => SOME (x, (xs, xss))
           | NONE => case streamGet xss
                       of SOME (xs, xss) => get (xs, xss)
                        | NONE => NONE
  in  streamOfUnfold get (EOS, xss)
  end
(* type declarations for consistency checking *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* type declarations for consistency checking *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* streams 650d *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* type declarations for consistency checking *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* streams 650e *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* type declarations for consistency checking *)
val _ = op @@@ : 'a stream * 'a stream -> 'a stream
(* error handling 651a *)
datatype 'a error = OK of 'a | ERROR of string
(* error handling 651b *)
infix 1 >>=
fun (OK x)      >>= k  =  k x
  | (ERROR msg) >>= k  =  ERROR msg
(* type declarations for consistency checking *)
val _ = op >>= : 'a error * ('a -> 'b error) -> 'b error
(* error handling 652a *)
infix 1 >>=+
fun e >>=+ k'  =  e >>= OK o k'
(* type declarations for consistency checking *)
val _ = op >>=+ : 'a error * ('a -> 'b) -> 'b error
(* error handling 652b *)
fun errorList es =
  let fun cons (OK x, OK xs) = OK (x :: xs)
        | cons (ERROR m1, ERROR m2) = ERROR (m1 ^ "; " ^ m2)
        | cons (ERROR m, OK _) = ERROR m
        | cons (OK _, ERROR m) = ERROR m
  in  foldr cons (OK []) es
  end
(* parsing combinators 652c *)
type ('a, 'b) xformer = 
  'a stream -> ('b error * 'a stream) option
(* type declarations for consistency checking *)
val _ = op errorList : 'a error list -> 'a list error
(* type declarations for consistency checking *)
type ('a, 'b) xformer = ('a, 'b) xformer
(* parsing combinators 653a *)
fun pure y = fn xs => SOME (OK y, xs)
(* type declarations for consistency checking *)
val _ = op pure : 'b -> ('a, 'b) xformer
(* parsing combinators 653b *)
infix 3 <*>
fun tx_f <*> tx_b =
  fn xs => case tx_f xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK f, xs) =>
                  case tx_b xs
                    of NONE => NONE
                     | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
                     | SOME (OK y, xs) => SOME (OK (f y), xs)
(* type declarations for consistency checking *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* parsing combinators 653c *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* type declarations for consistency checking *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* parsing combinators 654a *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* type declarations for consistency checking *)
val _ = op fst    : ('a * 'b) -> 'a
val _ = op snd    : ('a * 'b) -> 'b
val _ = op pair   : 'a -> 'b -> 'a * 'b
val _ = op curry  : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
val _ = op curry3 : ('a * 'b * 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)
(* parsing combinators 654b *)
infix 1 <|>
fun t1 <|> t2 = (fn xs => case t1 xs of SOME y => SOME y | NONE => t2 xs) 
(* type declarations for consistency checking *)
val _ = op <|> : ('a, 'b) xformer * ('a, 'b) xformer -> ('a, 'b) xformer
(* parsing combinators 655a *)
infix 3 <* *>
fun p1 <*  p2 = curry fst <$> p1 <*> p2
fun p1  *> p2 = curry snd <$> p1 <*> p2

infixr 4 <$
fun v <$ p = (fn _ => v) <$> p
(* type declarations for consistency checking *)
val _ = op <*  : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'b) xformer
val _ = op  *> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
val _ = op <$  : 'b               * ('a, 'c) xformer -> ('a, 'b) xformer
(* parsing combinators 655b *)
fun one xs = case streamGet xs
               of NONE => NONE
                | SOME (x, xs) => SOME (OK x, xs)
(* type declarations for consistency checking *)
val _ = op one : ('a, 'a) xformer
(* parsing combinators 655c *)
fun eos xs = case streamGet xs
               of NONE => SOME (OK (), EOS)
                | SOME _ => NONE
(* type declarations for consistency checking *)
val _ = op eos : ('a, unit) xformer
(* parsing combinators 655d *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* type declarations for consistency checking *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* parsing combinators 656a *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* type declarations for consistency checking *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* parsing combinators 656b *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* type declarations for consistency checking *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* parsing combinators 656c *)
fun oneEq x = sat (fn x' => x = x') one
(* type declarations for consistency checking *)
val _ = op oneEq : ''a -> (''a, ''a) xformer
(* parsing combinators 657a *)
infixr 4 <$>?
fun f <$>? tx =
  fn xs => case tx xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK y, xs) =>
                  case f y
                    of NONE => NONE
                     | SOME z => SOME (OK z, xs)
(* type declarations for consistency checking *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* parsing combinators 657b *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* type declarations for consistency checking *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* parsing combinators 657c *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* type declarations for consistency checking *)
val _ = op notFollowedBy : ('a, 'b) xformer -> ('a, unit) xformer
(* parsing combinators 657d *)
fun many t = 
  curry (op ::) <$> t <*> (fn xs => many t xs) <|> pure []
(* type declarations for consistency checking *)
val _ = op many  : ('a, 'b) xformer -> ('a, 'b list) xformer
(* parsing combinators 658a *)
fun many1 t = 
  curry (op ::) <$> t <*> many t
(* type declarations for consistency checking *)
val _ = op many1 : ('a, 'b) xformer -> ('a, 'b list) xformer
(* parsing combinators 658b *)
fun optional t = 
  SOME <$> t <|> pure NONE
(* type declarations for consistency checking *)
val _ = op optional : ('a, 'b) xformer -> ('a, 'b option) xformer
(* parsing combinators 658c *)
infix 2 <*>!
fun tx_ef <*>! tx_x =
  fn xs => case (tx_ef <*> tx_x) xs
             of NONE => NONE
              | SOME (OK (OK y),      xs) => SOME (OK y,      xs)
              | SOME (OK (ERROR msg), xs) => SOME (ERROR msg, xs)
              | SOME (ERROR msg,      xs) => SOME (ERROR msg, xs)
infixr 4 <$>!
fun ef <$>! tx_x = pure ef <*>! tx_x
(* type declarations for consistency checking *)
val _ = op <*>! : ('a, 'b -> 'c error) xformer * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
val _ = op <$>! : ('b -> 'c error)             * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
(* support for lexical analysis 659a *)
type 'a lexer = (char, 'a) xformer
(* type declarations for consistency checking *)
type 'a lexer = 'a lexer
(* support for lexical analysis 659b *)
fun isDelim c = Char.isSpace c orelse Char.contains "();" c
(* type declarations for consistency checking *)
val _ = op isDelim : char -> bool
(* support for lexical analysis 659c *)
val whitespace = many (sat Char.isSpace one)
(* type declarations for consistency checking *)
val _ = op whitespace : char list lexer
(* support for lexical analysis 660a *)
fun intChars isDelim = 
  (curry (op ::) <$> oneEq #"-" <|> pure id) <*> many1 (sat Char.isDigit one) <*
                                                                                
  notFollowedBy (sat (not o isDelim) one)
(* type declarations for consistency checking *)
val _ = op intChars     : (char -> bool) -> char list lexer
(* support for lexical analysis 660b *)
fun intFromChars (#"-" :: cs) = 
      intFromChars cs >>=+ ~
  | intFromChars cs =
      (OK o valOf o Int.fromString o implode) cs
      handle Overflow => ERROR
                        "this interpreter can't read arbitrarily large integers"
(* type declarations for consistency checking *)
val _ = op intFromChars : char list -> int error
(* support for lexical analysis 660c *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* type declarations for consistency checking *)
val _ = op intToken : (char -> bool) -> int lexer
(* support for parsing 660d *)
(* token, isLiteral, and
   tokenString can be defined
   differently in each language *)
(* support for parsing 661a *)
type srcloc = string * int
fun srclocString (source, line) =
  source ^ ", line " ^ Int.toString line
(* support for parsing 661b *)
fun errorAt msg loc =
  ERROR (msg ^ " in " ^ srclocString loc)
(* support for parsing 661c *)
type 'a located = srcloc * 'a
(* type declarations for consistency checking *)
type token = token
val _ = op isLiteral : string -> token -> bool
val _ = op tokenString : token -> string
(* type declarations for consistency checking *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* type declarations for consistency checking *)
val _ = op errorAt : string -> srcloc -> 'a error
(* type declarations for consistency checking *)
type 'a located = 'a located
(* support for parsing 661d *)
fun locatedStream (streamname, inputs) =
  let val locations = streamZip (streamRepeat streamname,
                                 streamOfUnfold (fn n => SOME (n, n+1)) 1)
  in  streamZip (locations, inputs)
  end
(* type declarations for consistency checking *)
val _ = op locatedStream : string * line stream -> line located stream
(* support for parsing 662a *)
datatype 'a inline
  = EOL of int (* number of the line that ends here *)
  | INLINE of 'a

fun drainLine EOS = EOS
  | drainLine (SUSPENDED s)     = drainLine (force s)
  | drainLine (EOL _    ::: xs) = xs
  | drainLine (INLINE _ ::: xs) = drainLine xs
(* parsing utilities 662b *)
type 'a parser = (token located inline, 'a) xformer
(* parsing utilities 663a *)
local 
  fun asEol (EOL n) = SOME n
    | asEol (INLINE _) = NONE
  fun asInline (INLINE x) = SOME x
    | asInline (EOL _)    = NONE
in
  fun eol    xs = (asEol <$>? one) xs
  fun inline xs = (many eol *> asInline <$>? one) xs
end

val token    =         snd <$> inline  : token parser
val srcloc   = rewind (fst <$> inline) : srcloc parser
val noTokens = notFollowedBy token : unit parser
(* type declarations for consistency checking *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* type declarations for consistency checking *)
type 'a parser = 'a parser
(* type declarations for consistency checking *)
val _ = op eol      : ('a inline, int) xformer
val _ = op inline   : ('a inline, 'a)  xformer
val _ = op token    : token parser
val _ = op srcloc   : srcloc parser
val _ = op noTokens : unit parser
(* parsing utilities 663b *)
fun @@ p = pair <$> srcloc <*> p
(* type declarations for consistency checking *)
val _ = op @@ : 'a parser -> 'a located parser
(* parsing utilities 663c *)

infix 0 <?>
fun p <?> expected = p <|> errorAt ("expected " ^ expected) <$>! srcloc
(* type declarations for consistency checking *)
val _ = op <?> : 'a parser * string -> 'a parser
(* parsing utilities 664a *)
infix 4 <!>
fun p <!> msg =
  fn tokens => (case p tokens
                  of SOME (OK _, unused) =>
                       (case peek srcloc tokens
                          of SOME loc => SOME (errorAt msg loc, unused)
                           | NONE => NONE)
                   | _ => NONE)
(* parsing utilities 664b *)
fun literal s =
  ignore <$> sat (isLiteral s) token
(* type declarations for consistency checking *)
val _ = op <!> : 'a parser * string -> 'b parser
(* type declarations for consistency checking *)
val _ = op literal : string -> unit parser
(* parsing utilities 664c *)
infix  6 --<
infixr 7 >-- 
    (* if we want to mix these operators, they can't have equal precedence *)
fun (a >-- p) = literal a *> p
fun (p --< a) = p <* literal a
(* type declarations for consistency checking *)
val _ = op >-- : string    * 'a parser -> 'a parser
val _ = op --< : 'a parser * string    -> 'a parser
(* parsing utilities 665 *)

fun bracket keyword expected p = 
  "(" >-- literal keyword *> (p --< ")" <|>
                              errorAt ("expected " ^ expected) <$>!
                                                               scanToCloseParen)
and scanToCloseParen tokens = 
  let val loc = getOpt (peek srcloc tokens, ("end of stream", 9999))
      fun scan lpcount tokens =
        (* lpcount is the number of unmatched left parentheses *)
        case tokens
          of EOL _         ::: tokens => scan lpcount tokens
           | INLINE (_, t) ::: tokens =>
                                  if isLiteral "(" t then scan (lpcount+1)
                                                                          tokens
                                  else if isLiteral ")" t then
                                      if lpcount = 0 then SOME (OK loc, tokens)
                                      else scan (lpcount-1) tokens
                                  else scan lpcount tokens
           | EOS         => SOME (errorAt "unmatched (" loc, EOS)
           | SUSPENDED s => scan lpcount (force s)
  in  scan 0 tokens
  end
(* type declarations for consistency checking *)
val _ = op bracket          : string -> string -> 'a parser -> 'a parser
val _ = op scanToCloseParen : srcloc parser
(* parsing utilities 666a *)
fun nodups (what, where') (loc, names) =
  let fun dup [] = OK names
        | dup (x::xs) = if List.exists (fn y : string => y = x) xs then
                          errorAt (what ^ " " ^ x ^ " appears twice in " ^
                                                                     where') loc
                        else
                          dup xs
  in  dup names
  end
(* type declarations for consistency checking *)
val _ = op nodups : string * string -> srcloc * name list -> name list error
(* code used to debug parsers 666b *)
val safeTokens : token located inline stream -> token list =
  let fun tokens (seenEol, seenUnforced) =
            let fun get (EOL _         ::: ts) = if seenUnforced then []
                                                 else tokens (true, false) ts
                  | get (INLINE (_, t) ::: ts) = t :: get ts
                  | get  EOS                   = []
                  | get (SUSPENDED (ref (PRODUCED ts))) = get ts
                  | get (SUSPENDED s) = if seenEol then []
                                        else tokens (false, true) (force s)
            in   get
            end
  in  tokens (false, false)
  end
(* type declarations for consistency checking *)
val _ = op safeTokens : token located inline stream -> token list
(* code used to debug parsers 667a *)
fun wrap what p tokens =
  let fun t tok = " " ^ tokenString tok
      val _ = app print ["Looking for ", what, " at"]
      val _ = app (print o t) (safeTokens tokens)
      val _ = print "\n"
      val answer = p tokens
      val _ = app print [case answer of NONE => "Didn't find " | SOME _ =>
                                                                       "Found ",
                         what, "\n"]
  in  answer
  end handle e => ( app print ["Search for ", what, " raised ", exnName e, "\n"]
                  ; raise e)

fun wrap what p = p 
(* type declarations for consistency checking *)
val _ = op wrap : string -> 'a parser -> 'a parser
(* an interactive reader 667b *)
fun echoTagStream lines = 
  let fun echoIfTagged line =
        if (String.substring (line, 0, 2) = ";#" handle _ => false) then
          print line
        else
          ()
  in  postStream (lines, echoIfTagged)
  end
(* type declarations for consistency checking *)
val _ = op echoTagStream : line stream -> line stream 
(* an interactive reader 667c *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* type declarations for consistency checking *)
val _ = op errorln : string -> unit
(* an interactive reader 668a *)
fun stripErrors xs =
  let fun next xs =
        case streamGet xs
          of SOME (ERROR msg, xs) => (errorln ("error: " ^ msg); next xs)
           | SOME (OK x, xs) => SOME (x, xs)
           | NONE => NONE
  in  streamOfUnfold next xs
  end
(* type declarations for consistency checking *)
val _ = op stripErrors : 'a error stream -> 'a stream
(* an interactive reader 668b *)
fun lexLineWith lexer =
  stripErrors o streamOfUnfold lexer o streamOfList o explode
(* type declarations for consistency checking *)
val _ = op lexLineWith : token lexer -> line -> token stream
(* an interactive reader 668c *)
fun parseWithErrors parser =
  let fun adjust (SOME (ERROR msg, tokens)) = SOME (ERROR msg, drainLine tokens)
        | adjust other = other
  in  streamOfUnfold (adjust o parser)
  end
(* type declarations for consistency checking *)
val _ = op parseWithErrors : 'a parser -> token located inline stream -> 'a
                                                                    error stream
(* an interactive reader 668d *)
type prompts   = { ps1 : string, ps2 : string }
val stdPrompts = { ps1 = "-> ", ps2 = "   " }
val noPrompts  = { ps1 = "", ps2 = "" }
(* type declarations for consistency checking *)
type prompts = prompts
val _ = op stdPrompts : prompts
val _ = op noPrompts  : prompts
(* an interactive reader 669 *)
fun 'a reader (lexer, parser) prompts (name, lines) =
  let val { ps1, ps2 } = prompts
      val thePrompt = ref ps1
      fun setPrompt ps = fn _ => thePrompt := ps

      val lines = preStream (fn () => print (!thePrompt), echoTagStream lines)

      fun lexAndDecorate (loc, line) =
        let val tokens = postStream (lexLineWith lexer line, setPrompt ps2)
        in  streamMap INLINE (streamZip (streamRepeat loc, tokens)) @@@
            streamOfList [EOL (snd loc)]
        end

      val edefs : 'a error stream = 
        (parseWithErrors parser o streamConcatMap lexAndDecorate o locatedStream
                                                                               )
        (name, lines)
(* type declarations for consistency checking *)
val _ = op reader : token lexer * 'a parser -> prompts -> string * line stream
                                                                    -> 'a stream
val _ = op lexAndDecorate : srcloc * line -> token located inline stream
  in  
      stripErrors (preStream (setPrompt ps1, edefs))
  end 
(* lexical analysis ((upr)) 711b *)
fun symbolic ":-" = RESERVED ":-"
  | symbolic "."  = RESERVED "."
  | symbolic "|"  = RESERVED "|"
  | symbolic "!"  = LOWER "!"
  | symbolic s    = SYMBOLIC s
fun lower "is" = RESERVED "is"
  | lower s    = LOWER s
(* lexical analysis ((upr)) 711c *)
fun anonymousVar () =
  case freshVar ""
    of VAR v => UPPER v
     | _ => let exception ThisCan'tHappen in raise ThisCan'tHappen end
(* lexical analysis ((upr)) 711d *)
local
  (* character-classification functions for \uprolog 711a *)
  val symbols = explode "!%^&*-+:=|~<>/?`$\\"
  fun isSymbol c = List.exists (fn c' => c' = c) symbols
  fun isIdent  c = Char.isAlphaNum c orelse c = #"_"
  fun isDelim  c = not (isIdent c orelse isSymbol c)
  (* lexical utility functions for \uprolog 712a *)
  fun underscore _ [] = OK (anonymousVar ())
    | underscore c cs = ERROR ("name may not begin with underscore at " ^
                                   implode (c::cs))

  fun int cs [] = intFromChars cs >>=+ INT_TOKEN
    | int cs ids = 
        ERROR ("integer literal " ^ implode cs ^
               " may not be followed by '" ^ implode ids ^ "'")
  (* type declarations for consistency checking *)
  val _ = op underscore : char      -> char list -> token error
  val _ = op int        : char list -> char list -> token error
  (* lexical utility functions for \uprolog 712b *)
  fun unrecognized (ERROR _) = let exception Can'tHappen in raise Can'tHappen
                                                                             end
    | unrecognized (OK cs) =
        case cs
          of []        => NONE
           | #";" :: _ => let exception Can'tHappen in raise Can'tHappen end
           | _ =>
               SOME (ERROR ("invalid initial character in `" ^ implode cs ^ "'")
                                                                          , EOS)
  (* type declarations for consistency checking *)
  val _ = op unrecognized : char list error -> ('a error * 'a error stream)
                                                                          option
  (* lexical utility functions for \uprolog 712c *)
  fun nextline (file, line) = (file, line+1)
  (* type declarations for consistency checking *)
  val _ = op nextline : srcloc -> srcloc
in
  (* lexical analyzers for for \uprolog 712d *)
  type 'a prolog_lexer = (char inline, 'a) xformer
  fun char chars =
    case streamGet chars
      of SOME (INLINE c, chars) => SOME (OK c, chars) 
       | _ => NONE
  fun eol chars =
    case streamGet chars
      of SOME (EOL _, chars) => SOME (OK (), chars)
       | _ => NONE
  (* lexical analyzers for for \uprolog 713a *)
  fun charEq c =
    sat (fn c' => c = c') char
  fun manySat p =
    many (sat p char)

  val whitespace =
    manySat Char.isSpace
  val intChars = 
    (curry op :: <$> charEq #"-" <|> pure id) <*> many1 (sat Char.isDigit char)
  (* type declarations for consistency checking *)
  type 'a prolog_lexer = 'a prolog_lexer
  val _ = op char : char prolog_lexer
  val _ = op eol  : unit prolog_lexer
  (* type declarations for consistency checking *)
  val _ = op charEq     : char -> char prolog_lexer
  val _ = op manySat    : (char -> bool) -> char list prolog_lexer
  val _ = op whitespace : char list prolog_lexer
  val _ = op intChars   : char list prolog_lexer
  (* lexical analyzers for for \uprolog 713b *)
  val ordinaryToken =
        underscore            <$> charEq #"_" <*>! manySat isIdent
    <|> (RESERVED o str)      <$> sat isDelim char                    
    <|> int                   <$> intChars    <*>! manySat isIdent
    <|> (symbolic o implode)  <$> many1 (sat isSymbol char)
    <|> curry (lower o implode o op ::) <$> sat Char.isLower char <*> manySat
                                                                         isIdent
    <|> curry (UPPER o implode o op ::) <$> sat Char.isUpper char <*> manySat
                                                                         isIdent
    <|> unrecognized o fst o valOf o many char
  (* lexical analyzers for for \uprolog 713c *)
  fun tokenAt loc cs =  (* eta-expanded to avoid infinite regress *)
    (whitespace *> (   charEq #"/" *> charEq #"*" *> skipComment loc loc
                   <|> charEq #";" *> many char *> eol *> tokenAt (nextline loc)
                   <|>                             eol *> tokenAt (nextline loc)
                   <|> (loc, EOF) <$ eos
                   <|> pair loc <$> ordinaryToken
                   )) cs
  and skipComment start loc cs =
    (   charEq #"*" *> charEq #"/" *> tokenAt loc
    <|> char *> skipComment start loc
    <|> eol  *> skipComment start (nextline loc)
    <|> id <$>! pure (ERROR ("end of file looking for */ to close comment in " ^
                             srclocString start))
    ) cs
  (* type declarations for consistency checking *)
  val _ = op ordinaryToken : token prolog_lexer
  (* type declarations for consistency checking *)
  val _ = op tokenAt     : srcloc -> token located prolog_lexer
  val _ = op skipComment : srcloc -> srcloc -> token located prolog_lexer
end


(*****************************************************************)
(*                                                               *)
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* parsing ((upr)) 714a *)
val symbol = (fn SYMBOLIC  s => SOME s | _ => NONE) <$>? token
val upper  = (fn UPPER     s => SOME s | _ => NONE) <$>? token
val lower  = (fn LOWER     s => SOME s | _ => NONE) <$>? token
val int    = (fn INT_TOKEN n => SOME n | _ => NONE) <$>? token
(* type declarations for consistency checking *)
val _ = op symbol : string parser
val _ = op upper  : string parser
val _ = op lower  : string parser
val _ = op int    : int    parser
(* parsing ((upr)) 714b *)
val notSymbol =
  symbol <!> "arithmetic expressions must be parenthesized" <|>
  pure ()
(* type declarations for consistency checking *)
val _ = op notSymbol : unit parser
(* parsing ((upr)) 714c *)
fun nilt tokens = pure (APPLY ("nil", [])) tokens
fun cons (x, xs) = APPLY ("cons", [x, xs])
(* type declarations for consistency checking *)
val _ = op nilt : term parser
val _ = op cons : term * term -> term
(* parsing ((upr)) 714d *)
val variable        = upper
val binaryPredicate = symbol
val functr          = lower
fun commas p = 
  curry op :: <$> p <*> many ("," >-- p)
(* type declarations for consistency checking *)
val _ = op variable        : string parser
val _ = op binaryPredicate : string parser
val _ = op functr          : string parser
val _ = op commas : 'a parser -> 'a list parser
(* parsing ((upr)) 715a *)
fun term tokens = 
  (   "[" >-- ((fn elems => fn tail => foldr cons tail elems) <$> 
                    commas term <*> ("|" >-- (term <?> "list element") <|> nilt)
              <|> nilt
              ) --< "]"
  <|> (fn a => fn t => APPLY ("is", [a, t])) <$> atom --< "is" <*> (term <?>
                                                                         "term")
  <|> (fn l => fn f => fn r => APPLY (f, [l, r])) <$>
      atom <*> binaryPredicate <*> (atom <?> "atom") <* notSymbol
  <|> atom 
  ) 
  tokens
and atom tokens = 
  (   curry APPLY <$> functr <*> (   "(" >-- commas (term <?> "term") --< ")" 
                                 <|> pure []
                                 )
  <|> VAR     <$> variable
  <|> LITERAL <$> int
  <|> "(" >-- term --< ")"
  )
  tokens
(* type declarations for consistency checking *)
val _ = op term   : term parser
val _ = op atom   : term parser
val _ = op commas : 'a parser -> 'a list parser
(* parsing ((upr)) 715b *)
fun asGoal _   (APPLY g) = OK g
  | asGoal loc (VAR v)   = 
      errorAt ("Variable " ^ v ^ " cannot be a predicate") loc
  | asGoal loc (LITERAL n) =
      errorAt ("Integer " ^ Int.toString n ^ " cannot be a predicate") loc

val goal = asGoal <$> srcloc <*>! term 
(* type declarations for consistency checking *)
val _ = op asGoal : srcloc -> term -> goal error
val _ = op goal   : goal parser
(* parsing ((upr)) 716a *)
datatype concrete
  = BRACKET of string 
  | CLAUSE  of goal * goal list option
  | GOALS   of goal list

val notClosing = sat (fn RESERVED "]" => false | _ => true) token

val concrete = 
     (BRACKET o concat o map tokenString) <$> "[" >-- many notClosing --< "]"
 <|> curry CLAUSE <$> goal <*> ":-" >-- (SOME <$> commas goal)
 <|> GOALS <$> commas goal
(* type declarations for consistency checking *)
type concrete = concrete
val _ = op concrete : concrete parser
(* parsing ((upr)) 716b *)
datatype mode = QMODE | RMODE

fun mprompt RMODE = "-> "
  | mprompt QMODE = "?- "
(* type declarations for consistency checking *)
type mode = mode
val _ = op mprompt : mode -> string
(* parsing ((upr)) 716c *)
datatype cq_or_mode
  = CQ of cq
  | NEW_MODE of mode
(* type declarations for consistency checking *)
type cq_or_mode = cq_or_mode
(* parsing ((upr)) 717a *)
fun interpretConcrete mode =
  let val (newMode, cq, err) = (OK o NEW_MODE, OK o CQ, ERROR)
  in  fn c =>
        case (mode, c)
          of (_, BRACKET "rule")     => newMode RMODE
           | (_, BRACKET "fact")     => newMode RMODE
           | (_, BRACKET "user")     => newMode RMODE
           | (_, BRACKET "clause")   => newMode RMODE
           | (_, BRACKET "query")    => newMode QMODE
           | (_, BRACKET s)          => cq (USE s)
           | (RMODE, CLAUSE (g, ps)) => cq (ADD_CLAUSE (g :- getOpt (ps, [])))
           | (RMODE, GOALS [g])      => cq (ADD_CLAUSE (g :- []))
           | (RMODE, GOALS _ ) =>
                 err ("You cannot enter a query in clause mode; " ^
                      "to change modes, type `[query].'")
           | (QMODE, GOALS gs)           => cq (QUERY gs)
           | (QMODE, CLAUSE (g, NONE))   => cq (QUERY [g])
           | (QMODE, CLAUSE (_, SOME _)) => 
                 err ("You cannot enter a new clause in query mode; " ^
                      "to change modes, type `[rule].'")
  end                 
(* type declarations for consistency checking *)
val _ = op interpretConcrete : mode -> concrete -> cq_or_mode error
(* parsing ((upr)) 717b *)
val skippable = 
  (fn SYMBOLIC "." => NONE | EOF => NONE | t => SOME t) <$>? token

fun badConcrete (loc, skipped) last =
  ERROR (srclocString loc ^ ": expected clause or query; skipping" ^
         concat (map (fn t => " " ^ tokenString t) (skipped @ last)))

fun cq_or_mode mode = interpretConcrete mode <$>!
  (   concrete --< "."
  <|> badConcrete <$> @@ (many  skippable) <*>! ([RESERVED "."] <$ literal ".")
  <|> badConcrete <$> @@ (many1 skippable) <*>! pure []  (* skip to EOF *)
  )
(* type declarations for consistency checking *)
val _ = op cq_or_mode : mode -> cq_or_mode parser
(* parsing ((upr)) 718a *)
fun prologReader noisy initialMode (name, lines) =
  let val (ps1, ps2) = (mprompt initialMode, "   ")
      val thePrompt = ref ""  (* no prompt unless noisy *)
      val setPrompt = if noisy then (fn s => thePrompt := s) else (fn _ => ())

      type read_state = string * mode * token located inline stream
      (* utility functions for [[prologReader]] 718b *)
      fun startsWithEOF tokens =
        case streamGet tokens
          of SOME (INLINE (_, EOF), _) => true
           | _ => false
      (* type declarations for consistency checking *)
      val _ = op startsWithEOF : token located inline stream -> bool
      (* utility functions for [[prologReader]] 719a *)
      fun skipPastDot tokens =
        case streamGet tokens
          of SOME (INLINE (_, RESERVED "."), tokens) => tokens
           | SOME (INLINE (_, EOF), tokens) => tokens
           | SOME (_, tokens) => skipPastDot tokens
           | NONE => tokens
      (* type declarations for consistency checking *)
      val _ = op skipPastDot : token located inline stream -> token located
                                                                   inline stream
      (* utility functions for [[prologReader]] 719b *)
      fun getCq (ps1, mode, tokens) =
        ( setPrompt ps1
        ; if startsWithEOF tokens then
            NONE
          else
            case cq_or_mode mode tokens
              of SOME (OK (CQ cq),         tokens) => SOME (cq, (ps1, mode,
                                                                        tokens))
               | SOME (OK (NEW_MODE mode), tokens) => getCq (mprompt mode, mode,
                                                                         tokens)
               | SOME (ERROR msg,          tokens) => 
                                               ( errorln ("error: " ^ msg)
                                               ; getCq (ps1, mode, skipPastDot
                                                                         tokens)
                                               )
               | NONE => (* fail epically with a diagnostic about [[tokens]] 719
                                                                            c *)
                         let exception ThisCan'tHappenCqParserFailed
                             val tokensStrings = map (fn t => " " ^ tokenString
                                                  t) o valOf o peek (many token)
                             val _ = app print (tokensStrings tokens)
                         in  raise ThisCan'tHappenCqParserFailed
                         end
        )                 
      (* type declarations for consistency checking *)
      val _ = op getCq : read_state -> (cq * read_state) option

      val lines = preStream (fn () => print (!thePrompt), echoTagStream lines)

      val chars = 
        streamConcatMap
        (fn (loc, s) => streamOfList (map INLINE (explode s) @ [EOL (snd loc)]))
        (locatedStream (name, lines))

      fun getLocatedToken (loc, chars) =
        (case tokenAt loc chars
           of SOME (OK (loc, t), chars) => SOME (OK (loc, t), (loc, chars))
            | SOME (ERROR msg,   chars) => SOME (ERROR msg,   (loc, chars))
            | NONE => NONE
        ) before setPrompt ps2

      val tokens = stripErrors (streamOfUnfold getLocatedToken ((name, 1), chars
                                                                              ))

(* type declarations for consistency checking *)
val _ = op prologReader : bool -> mode -> string * string stream -> cq stream
type read_state  = read_state  fun zz__checktyperead_state (x : read_state ) = (
                               x :  string * mode * token located inline stream)
val _ = op getCq : read_state -> (cq * read_state) option
  in  streamOfUnfold getCq (ps1, initialMode, streamMap INLINE tokens)
  end 


(*****************************************************************)
(*                                                               *)
(*   IMPLEMENTATION OF [[USE]]                                   *)
(*                                                               *)
(*****************************************************************)

(* implementation of [[use]] 222a *)
fun use readEvalPrint syntax filename rho =
      let val fd = TextIO.openIn filename
          val defs = reader syntax noPrompts (filename, streamOfLines fd)
          fun writeln s = app print [s, "\n"]
          fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      in  readEvalPrint (defs, writeln, errorln) rho
          before TextIO.closeIn fd
      end 


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVES                                                  *)
(*                                                               *)
(*****************************************************************)

(* primitives ((upr)) 558a *)
exception RuntimeError of string
fun eval (LITERAL n) = n
  | eval (APPLY ("+", [x, y])) = eval x  +  eval y
  | eval (APPLY ("*", [x, y])) = eval x  *  eval y
  | eval (APPLY ("-", [x, y])) = eval x  -  eval y
  | eval (APPLY ("/", [x, y])) = eval x div eval y
  | eval (APPLY ("-", [x]))    = ~ (eval x)
  | eval (APPLY (f, _))        = 
      raise RuntimeError (f ^ " is not an arithmetic predicate " ^
                          "or is used with wrong arity")
  | eval (VAR v) = raise RuntimeError ("Used uninstantiated variable " ^ v ^
                                       " in arithmetic expression")
(* type declarations for consistency checking *)
val _ = op eval : term -> int
(* primitives ((upr)) 558b *)
fun is [x, e] succ fail = (succ (unifyTerm (x, LITERAL (eval e))) fail
                           handle Unify => fail())
  | is _      _    fail = fail ()
(* primitives ((upr)) 558d *)
fun compare name cmp [LITERAL n, LITERAL m] succ fail =
      if cmp (n, m) then succ idsubst fail else fail ()
  | compare name _ [_, _] _ _ =
      raise RuntimeError ("Used comparison " ^ name ^ " on non-integer term")
  | compare name _ _ _ _ =
      raise RuntimeError ("this can't happen---non-binary comparison?!")


(*****************************************************************)
(*                                                               *)
(*   TRACING FUNCTIONS                                           *)
(*                                                               *)
(*****************************************************************)

(* tracing functions 583 *)
fun logSucc goal succ rho resume =
  ( app print ["SUCC: ", goalString goal, " becomes ", goalString (lift rho goal
                                                                        ), "\n"]
  ; succ rho resume
  )
fun logFail goal fail () = 
  ( app print ["FAIL: ", goalString goal, "\n"]
  ; fail ()
  )
fun logResume goal resume () = 
  ( app print ["REDO: ", goalString goal, "\n"]
  ; resume ()
  )
fun logSolve solve goal succ fail = 
  ( app print ["START: ", goalString goal, "\n"]
  ; solve goal succ fail
  )


(*****************************************************************)
(*                                                               *)
(*   SEARCH                                                      *)
(*                                                               *)
(*****************************************************************)

(* search ((prototype)) 555a *)
fun 'a query database =
  let val builtins = foldl (fn ((n, p), rho) => bind (n, p, rho))
                     emptyEnv ((* primops :: ((upr)) 557c *)
                               ("print", fn args => fn succ => fn fail =>
                                           ( app (fn x => (print (termString x);
                                                                print " ")) args
                                           ; print "\n"
                                           ; succ (fn x => x) fail
                                           )) ::
                               (* primops :: ((upr)) 558c *)
                               ("is", is) ::
                               (* primops :: ((upr)) 558e *)
                               ("<",  compare "<"  op < ) ::
                               (">",  compare ">"  op > ) ::
                               ("=<", compare "=<" op <= ) ::
                               (">=", compare ">=" op >= ) ::
                               (* primops :: ((upr)) 558f *)
                               ("!",   fn _ => raise RuntimeError
                              "The cut (!) must be added to the interpreter") ::
                               ("not", fn _ => raise RuntimeError
                  "The predicate `not' must be added to the interpreter") :: [])
      fun solveOne (goal as (func, args)) succ fail =
            find(func, builtins) args succ fail
            handle NotFound _ =>
              let fun search [] = fail ()
                    | search (clause :: clauses) =  
                        let fun resume() = search clauses
                            val conclusion :- premises = freshen clause
                            val theta = unify (goal, conclusion)
                        in  solveMany (map (lift theta) premises) theta succ
                                                                          resume
                        end
                        handle Unify => search clauses
(* type declarations for consistency checking *)
val _ = op query  : database -> goal list -> (subst -> (unit->'a) -> 'a) -> (
                                                                 unit->'a) -> 'a
val _ = op solveOne  : goal               -> (subst -> (unit->'a) -> 'a) -> (
                                                                 unit->'a) -> 'a
val _ = op solveMany : goal list -> subst -> (subst -> (unit->'a) -> 'a) -> (
                                                                 unit->'a) -> 'a
val _ = op search    : clause list -> 'a
              in  search (potentialMatches (goal, database))
              end
      and solveMany []            theta succ fail = succ theta fail
        | solveMany (goal::goals) theta succ fail =
            solveOne goal
            (fn theta' => fn resume =>
               solveMany (map (lift theta') goals) (theta' o theta) succ resume)
            fail
  in  fn gs => solveMany gs (fn x => x)
  end


(*****************************************************************)
(*                                                               *)
(*   INTERACTION                                                 *)
(*                                                               *)
(*****************************************************************)

(* interaction 557a *)
fun showAndContinue prompt theta gs =
  let fun showVar v = app print [v, " = ", termString (theta (VAR v))]
      val vars = foldr union emptyset (map freevarsGoal gs)
  in  case vars
        of [] => false
         | h :: t => ( showVar h
                     ; app (fn v => (print "\n"; showVar v)) t
                     ; if prompt then
                         case Option.map explode (TextIO.inputLine TextIO.stdIn)
                           of SOME (#";" :: _) => (print "\n"; true)
                            | _ => false
                       else
                         (print "\n"; false)
                     )
  end


(*****************************************************************)
(*                                                               *)
(*   EVALUATION                                                  *)
(*                                                               *)
(*****************************************************************)

(* evaluation ((upr)) 555b *)
fun evalcq prompt (t, database : database, echo) =
  case t
    of USE filename => ((* read from file [[filename]] 556a *)
                        let fun foldOverFileStream tx evalPrint rho filename =
                              let val fd = TextIO.openIn filename
                                  val stream = (tx (filename, streamOfLines fd))
                                  val cq = (print "getting first cq\n";
                                                               streamGet stream)
                                  val _ = app print ["got ", if isSome cq then
                                               "something" else "nothing", "\n"]
                              in  streamFold evalPrint rho stream
                                  before TextIO.closeIn fd
                              end 
                            fun writeln s = app print [s, "\n"]
                            fun errorln s = TextIO.output (TextIO.stdErr, s ^
                                                                           "\n")

                            val try = foldOverFileStream (prologReader false
                                                                          RMODE)
                                                         (evalPrint false (
                                                              writeln, errorln))
                                                         database

                        in  try filename          handle IO.Io _ => 
                            try (filename ^ ".P") handle IO.Io _ => 
                            try (filename ^ ".pl")
                        end) : database
     | ADD_CLAUSE c => addClause (c, database)
     | QUERY gs     => ((* query goals [[gs]] against [[database]] 556b *)
                        query database gs
                          (fn theta => fn resume =>
                             if showAndContinue prompt theta gs then resume()
                                                             else print "yes\n")
                          (fn () => print "no\n"); database)
(* evaluation ((upr)) 557b *)
and evalPrint prompt (echo, errmsg) (cq, database) =
  let fun continue msg = (errmsg msg; database)
  in  evalcq prompt (cq, database, echo)
      handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
      (* more read-eval-print handlers 222c *)
      (* more read-eval-print handlers 223a *)
      | Div               => continue "Division by zero"
      | Overflow          => continue "Arithmetic overflow"
      | RuntimeError msg  => continue ("run-time error: " ^ msg)
      | NotFound n        => continue ("variable " ^ n ^ " not found")
  end
(* type declarations for consistency checking *)
val _ = op evalcq : bool -> cq * database * (string->unit) -> database
(* type declarations for consistency checking *)
val _ = op showAndContinue : bool -> subst -> goal list -> bool
(* type declarations for consistency checking *)
val _ = op evalPrint : bool -> (string->unit) * (string->unit) -> cq * database
                                                                     -> database


(*****************************************************************)
(*                                                               *)
(*   PROLOG COMMAND LINE                                         *)
(*                                                               *)
(*****************************************************************)

(* Prolog command line 719d *)
fun runInterpreter noisy = 
  let fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val mode = if noisy then QMODE else RMODE
      val cqs  =
        prologReader noisy mode ("standard input", streamOfLines TextIO.stdIn)
  in  ignore (streamFold (evalPrint noisy (writeln, errorln)) emptyDatabase cqs)
  end 
(* Prolog command line 720a *)
fun runmain ["-q"]          = runInterpreter false
  | runmain []              = runInterpreter true
  | runmain ("-trace" :: t) = (tracer := app print; runmain t)
  | runmain _  =
      TextIO.output (TextIO.stdErr, "Usage: " ^ CommandLine.name() ^ " [-q]\n")
(* Prolog command line 720b *)
val _ = runmain (CommandLine.arguments())
