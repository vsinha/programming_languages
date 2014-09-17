(* tuscheme.sml 275a *)


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
exception TypeError of string


(*****************************************************************)
(*                                                               *)
(*   DEFINITION OF [[SEPARATE]]                                  *)
(*                                                               *)
(*****************************************************************)

(* definition of [[separate]] 218d *)
fun separate (zero, sep) =  (* print list with separator *)
  let fun s []     = zero
        | s [x]    = x
        | s (h::t) = h ^ sep ^ s t
  in  s
end
val spaceSep = separate ("", " ")  (* print separated by spaces *)


(*****************************************************************)
(*                                                               *)
(*   TYPES FOR {\TUSCHEME}                                       *)
(*                                                               *)
(*****************************************************************)

(* types for {\tuscheme} 258a *)
datatype kind = TYPE                          (* kind of all types *)
              | ARROW of kind list * kind     (* kind of many constructors *)
(* types for {\tuscheme} 260 *)
datatype tyex = TYCON  of name                (* type constructor *)
              | CONAPP of tyex * tyex list    (* type-level application *)
              | FORALL of name list * tyex
              | TYVAR  of name                (* type variable *)
(* types for {\tuscheme} 263c *)
(* printing types for {\tuscheme} 683 *)
fun typeString (TYCON c) = c
  | typeString (TYVAR a) = a
  | typeString (CONAPP (TYCON "function", [CONAPP (TYCON "tuple", args), result]
                                                                            )) =
      "(function (" ^ spaceSep (map typeString args) ^ ") " ^ typeString result
                                                                           ^ ")"
  | typeString (CONAPP (tau, [])) = "(" ^ typeString tau ^ ")"
  | typeString (CONAPP (tau, l)) =
      "(" ^ typeString tau ^ " " ^ spaceSep (map typeString l) ^ ")"
  | typeString (FORALL (l, tau)) =
      "(forall (" ^ spaceSep l ^ ") " ^ typeString tau ^ ")"
(* type declarations for consistency checking *)
val _ = op typeString : tyex -> string
(* types for {\tuscheme} 267b *)
val inttype  = TYCON "int"
val booltype = TYCON "bool"
val symtype  = TYCON "sym"
val unittype = TYCON "unit"
val tyvarA   = TYVAR "'a"
fun tupletype l = CONAPP (TYCON "tuple", l)
fun listtype ty = CONAPP (TYCON "list",[ty])
fun funtype (args, result) = CONAPP (TYCON "function", [tupletype args, result])
(* type declarations for consistency checking *)
val _ = op inttype   : tyex
val _ = op booltype  : tyex
val _ = op symtype   : tyex
val _ = op unittype  : tyex
val _ = op tyvarA    : tyex
val _ = op tupletype : tyex list -> tyex
val _ = op listtype  : tyex -> tyex
val _ = op funtype   : tyex list * tyex -> tyex


(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS                                            *)
(*                                                               *)
(*****************************************************************)

(* lexical analysis ((mlscheme)) 671a *)
datatype token = NAME    of string
               | INT     of int
               | SHARP   of bool
               | BRACKET of char (* ( or ) *)
               | QUOTE
(* lexical analysis ((mlscheme)) 671b *)
fun tokenString (NAME x)    = x
  | tokenString (INT  n)    = Int.toString n
  | tokenString (SHARP b)   = if b then "#t" else "#f"
  | tokenString (BRACKET c) = str c
  | tokenString (QUOTE)     = "'"

fun isLiteral s t = tokenString t = s
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
(* lexical analysis ((mlscheme)) 672a *)
local
  (* functions used in the lexer for \uscheme 672b *)
  fun atom "#t" = SHARP true
    | atom "#f" = SHARP false
    | atom x    = NAME x
  (* functions used in the lexer for \uscheme 672c *)
  fun noneIfLineEnds chars =
    case streamGet chars
      of NONE => NONE (* end of line *)
       | SOME (#";", cs) => NONE (* comment *)
       | SOME (c, cs) => 
           let val msg = "invalid initial character in `" ^
                         implode (c::listOfStream cs) ^ "'"
           in  SOME (ERROR msg, EOS)
           end
  (* type declarations for consistency checking *)
  val _ = op noneIfLineEnds : 'a lexer
in
  val schemeToken =
    whitespace *> (   BRACKET <$> oneEq #"("
                  <|> BRACKET <$> oneEq #")"
                  <|> QUOTE   <$  oneEq #"'"
                  <|> INT     <$> intToken isDelim
                  <|> (atom o implode) <$> many1 (sat (not o isDelim) one)
                  <|> noneIfLineEnds
                  )
(* type declarations for consistency checking *)
val _ = op schemeToken : token lexer
val _ = op atom : string -> token
end


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR {\TUSCHEME}                  *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values for {\tuscheme} 268a *)
datatype exp = LITERAL  of value
             | VAR      of name
             | SET      of name * exp
             | IFX      of exp * exp * exp
             | WHILEX   of exp * exp
             | BEGIN    of exp list
             | APPLY    of exp * exp list
             | LETX     of let_kind * (name * exp) list * exp
             | LAMBDA   of lambda_exp
             | TYLAMBDA of name list * exp
             | TYAPPLY  of exp * tyex list
and let_kind = LET | LETSTAR
and    value = NIL
             | BOOL      of bool   
             | NUM       of int
             | SYM       of name
             | PAIR      of value * value
             | CLOSURE   of lambda_value * value ref env
             | PRIMITIVE of primitive
withtype primitive    = value list -> value (* raises RuntimeError *)
     and lambda_exp   = (name * tyex) list * exp
     and lambda_value = name          list * exp

exception RuntimeError of string
(* abstract syntax and values for {\tuscheme} 268b *)
datatype def = VAL    of name * exp
             | VALREC of name * tyex * exp
             | EXP    of exp
             | DEFINE of name * tyex * lambda_exp
             | USE    of name


(*****************************************************************)
(*                                                               *)
(*   VALUES                                                      *)
(*                                                               *)
(*****************************************************************)

(* values ((mlscheme)) 216b *)



fun embedList []     = NIL
  | embedList (h::t) = PAIR (h, embedList t)
fun embedPredicate f = fn x => BOOL (f x)
fun bool (BOOL b) = b
  | bool _        = true
(* type declarations for consistency checking *)
val _ = op embedList      : value list -> value
val _ = op embedPredicate : ('a -> bool) -> ('a -> value)
val _ = op bool           : value -> bool
(* values ((mlscheme)) 217a *)
fun valueString (NIL)    = "()"
  | valueString (BOOL b) = if b then "#t" else "#f"
  | valueString (NUM n)  = String.map (fn #"~" => #"-" | c => c) (Int.toString n
                                                                               )
  | valueString (SYM v)  = v
  | valueString (PAIR (car, cdr))  = 
      let fun tail (PAIR (car, cdr)) = " " ^ valueString car ^ tail cdr
            | tail NIL = ")"
            | tail v = " . " ^ valueString v ^ ")"
      in  "(" ^ valueString car ^ tail cdr
      end
  | valueString (CLOSURE   _) = "<procedure>"
  | valueString (PRIMITIVE _) = "<procedure>"
(* type declarations for consistency checking *)
val _ = op valueString : value -> string


(*****************************************************************)
(*                                                               *)
(*   TYPE CHECKING FOR {\TUSCHEME}                               *)
(*                                                               *)
(*****************************************************************)

(* type checking for {\tuscheme} 264a *)
fun kindof (tau, Delta) =
  let (* internal function [[kind]] 264b *)
      fun kind (TYVAR a) =
            (find (a, Delta)
             handle NotFound _ => raise TypeError ("unknown type variable " ^ a)
                                                                               )
      (* internal function [[kind]] 264c *)
        | kind (TYCON c) =
            (find (c, Delta)
             handle NotFound _ => raise TypeError ("unknown type constructor " ^
                                                                             c))
      (* internal function [[kind]] 264d *)
        | kind (CONAPP (TYCON "tuple", actuals)) =
            if List.all (fn tau => kind tau = TYPE) actuals then
                TYPE
            else
                raise TypeError "tuple formed from non-types"
      (* internal function [[kind]] 265a *)
        | kind (CONAPP (tau, actuals)) =
            (case kind tau
               of ARROW (formals, result) =>
                    if formals = map kind actuals then
                        result
                    else
                        raise TypeError ("type constructor " ^ typeString tau ^
                                         " applied to the wrong arguments")
                | TYPE =>
                    raise TypeError ("tried to apply type " ^ typeString tau ^
                                     " as type constructor"))
      (* internal function [[kind]] 265b *)
        | kind (FORALL (alphas, tau)) =
            let val Delta' =
                  foldl (fn (a, Delta) => bind (a, TYPE, Delta)) Delta alphas
            in  case kindof (tau, Delta')
                  of TYPE    => TYPE
                   | ARROW _ => raise TypeError
                                      "quantifed a non-nullary type constructor"
            end
(* type declarations for consistency checking *)
val _ = op kindof : tyex * kind env -> kind
val _ = op kind   : tyex            -> kind
  in  kind tau
  end
(* type checking for {\tuscheme} 265c *)
fun asType (ty, Delta) =
  case kindof (ty, Delta)
    of TYPE    => ty
     | ARROW _ => raise TypeError ("used type constructor `" ^ typeString ty ^
                                   "' as a type")
(* type declarations for consistency checking *)
val _ = op asType : tyex * kind env -> tyex
(* type checking for {\tuscheme} 266a *)
fun tysubst (tau, varenv) =
  let fun subst (TYVAR a) = (find (a, varenv) handle NotFound _ => TYVAR a)
        | subst (TYCON c) = (TYCON c)
        | subst (CONAPP (tau, taus)) = CONAPP (subst tau, map subst taus)
        | subst (FORALL (alphas, tau)) =
            FORALL (alphas, tysubst (tau, bindList (alphas, map TYVAR alphas,
                                                                       varenv)))
(* type declarations for consistency checking *)
val _ = op tysubst : tyex * tyex env -> tyex
val _ = op subst   : tyex            -> tyex
  in  subst tau
  end
(* type checking for {\tuscheme} 266b *)
fun instantiate (FORALL (formals, tau), actuals, Delta) =
      (case List.find (fn t => kindof (t, Delta) <> TYPE) actuals
         of SOME t => raise TypeError ("instantiated at type constructor `" ^
                                       typeString t ^ "', which is not a type")
          | NONE =>
              (tysubst (tau, bindList (formals, actuals, emptyEnv))
               handle BindListLength =>
                 raise TypeError
                   "instantiated polymorphic term at wrong number of arguments")
                                                                               )
  | instantiate (tau, _, _) =
       raise TypeError ("tried to instantiate term of non-polymorphic type " ^
                        typeString tau)
(* type declarations for consistency checking *)
val _ = op instantiate : tyex * tyex list * kind env -> tyex
val _ = List.find : ('a -> bool) -> 'a list -> 'a option
(* type checking for {\tuscheme} 267a *)
fun eqType (TYCON c, TYCON c') = c = c'
  | eqType (CONAPP (tau, taus), CONAPP (tau', taus')) =
      eqType (tau, tau') andalso eqTypes (taus, taus')
  | eqType (FORALL (alphas, tau), FORALL (alphas', tau')) =
      (eqType (tau, tysubst (tau', bindList (alphas', map TYVAR alphas, emptyEnv
                                                                             )))
       handle BindListLength => false)
  | eqType (TYVAR a, TYVAR a') = a = a'
  | eqType _ = false
and eqTypes (t::taus, t'::taus') = eqType (t, t') andalso eqTypes (taus, taus')
  | eqTypes ([], []) = true
  | eqTypes _ = false
(* type declarations for consistency checking *)
val _ = op eqType  : tyex      * tyex      -> bool
val _ = op eqTypes : tyex list * tyex list -> bool
(* type checking for {\tuscheme} 271 *)
fun appearsUnprotectedIn (x, e) = 
  let fun evaluatesX (LITERAL n) = false
        | evaluatesX (VAR x') = x' = x
        | evaluatesX (SET (_, e)) = evaluatesX e
        | evaluatesX (WHILEX (e1, e2)) = evaluatesX e1 orelse evaluatesX e2
        | evaluatesX (APPLY (f, actuals)) =
            evaluatesX f orelse List.exists evaluatesX actuals
        | evaluatesX (LETX (LETSTAR, [], body)) = evaluatesX body
        | evaluatesX (LETX (LETSTAR, (x', e') :: bs, body)) =
            evaluatesX e' orelse
            (x <> x' andalso evaluatesX (LETX (LETSTAR, bs, body)))
        | evaluatesX (LETX (LET, bs, body)) = 
            List.exists (fn (_, e) => evaluatesX e) bs orelse
            (not (List.exists (fn (x', _) => x' = x) bs) andalso evaluatesX body
                                                                               )
        | evaluatesX (IFX (e1, e2, e3)) =
            evaluatesX e1 orelse evaluatesX e2 orelse evaluatesX e3
        | evaluatesX (BEGIN es) = List.exists evaluatesX es
        | evaluatesX (LAMBDA (formals, body)) = false
        | evaluatesX (TYAPPLY (e, args)) = evaluatesX e
        | evaluatesX (TYLAMBDA (alphas, e)) = evaluatesX e
  in  evaluatesX e
  end
(* type checking for {\tuscheme} ((prototype)) 272a *)
exception LeftAsExercise of string
fun elabdef _ = raise LeftAsExercise "elabdef"
(* type declarations for consistency checking *)
val _ = op elabdef : def * tyex env * kind env -> tyex env * string


(*****************************************************************)
(*                                                               *)
(*   PARSING FOR {\TUSCHEME}                                     *)
(*                                                               *)
(*****************************************************************)

(* parsing for {\tuscheme} 684a *)
val name    = (fn (NAME  n) => SOME n  | _ => NONE) <$>? token
val booltok = (fn (SHARP b) => SOME b  | _ => NONE) <$>? token
val int     = (fn (INT   n) => SOME n  | _ => NONE) <$>? token
val quote   = (fn (QUOTE)   => SOME () | _ => NONE) <$>? token

fun keyword syntax words =
  let fun isKeyword s = List.exists (fn s' => s = s') words
  in  (fn (NAME n) => if isKeyword n then SOME n else NONE | _ => NONE) <$>?
                                                                           token
  end

val expKeyword = keyword "type"       ["if", "while", "set", "begin", "lambda",
                                       "type-lambda", "let", "let*", "@"]
val tyKeyword  = keyword "expression" ["forall", "function"]

val tlformals = nodups ("formal type parameter", "type-lambda") <$>! @@ (many
                                                                           name)

fun nodupsty what (loc, xts) = nodups what (loc, map fst xts) >>=+ (fn _ => xts)
                                                        (* error on duplicate
                                                                        names *)

fun letDups LETSTAR (_, bindings) = OK bindings
  | letDups LET     bindings       = nodupsty ("bound variable", "let") bindings
(* parsing for {\tuscheme} 684b *)
val tyvar = quote *> (curry op ^ "'" <$> name <?>
                                               "type variable (got quote mark)")
  
fun checkedForall tyvars tau =
  nodups ("quantified type variable", "forall") tyvars >>=+ (fn a's =>
  FORALL (a's, tau))

fun ty tokens = (
     TYCON <$> name
 <|> TYVAR <$> tyvar
 <|> bracket "forall"    "(forall (tyvars) type)" 
                            (checkedForall <$> "(" >-- @@ (many tyvar) --< ")"
                                                                        <*>! ty)
 <|> bracket "function" "(function (types) type)"
                            (curry funtype <$> "(" >-- many ty --< ")" <*> ty)
 <|> badExpKeyword <$>! ("(" >-- @@ expKeyword <* scanToCloseParen)
 <|> curry CONAPP <$> "(" >-- ty <*> many ty --< ")" 
 <|> "(" >-- literal ")" <!> "empty type ()"
 <|> int <!> "expected type; found integer"
 <|> booltok <!> "expected type; found Boolean literal"
) tokens
and badExpKeyword (loc, bad) =
      errorAt ("looking for type but found `" ^ bad ^ "'") loc
(* parsing for {\tuscheme} 685 *)
val formal =
  "(" >-- ((fn tau => fn x => (x, tau)) <$> ty <*> name --< ")" <?>
                                                                 "(ty argname)")
val lformals = "(" >-- many formal --< ")"
val tformals = "(" >-- many tyvar  --< ")"

fun lambda xs exp =
      nodupsty ("formal parameter", "lambda") xs >>=+ (fn xs => LAMBDA (xs, exp)
                                                                               )
fun tylambda a's exp =
      nodups ("formal type parameter", "type-lambda") a's >>=+ (fn a's =>
      TYLAMBDA (a's, exp))

val br = bracket

fun exp tokens = (
     VAR              <$> name
 <|> (LITERAL o NUM)  <$> int
 <|> (LITERAL o BOOL) <$> booltok
 <|> LITERAL          <$> (quote *> sexp)
 <|> br "if"     "(if e1 e2 e3)"            (curry3 IFX     <$> exp  <*> exp <*>
                                                                            exp)
 <|> br "while"  "(while e1 e2)"            (curry  WHILEX  <$> exp  <*> exp)
 <|> br "set"    "(set x e)"                (curry  SET     <$> name <*> exp)
 <|> br "begin"  ""                         (       BEGIN   <$> many exp)
 <|> br "lambda" "(lambda (formals) body)"  (       lambda  <$> @@ lformals <*>!
                                                                            exp)
 <|> br "type-lambda" "(type-lambda (tyvars) body)"
                                            (       tylambda <$> @@ tformals
                                                                       <*>! exp)
 <|> br "let"    "(let (bindings) body)"    (letx   LET     <$> @@ bindings <*>!
                                                                            exp)
 <|> br "letrec" "(letrec (bindings) body)" (letrec <$> bindings <*>! exp)
 <|> br "let*"   "(let* (bindings) body)"   (letx   LETSTAR <$> @@ bindings <*>!
                                                                            exp)
 <|> br "@"      "(@ exp types)"            (curry  TYAPPLY <$> exp <*> many1 ty
                                                                               )
 <|> badTyKeyword <$>! ("(" >-- @@ tyKeyword <* scanToCloseParen)
 <|> "(" >-- literal ")" <!> "empty application"
 <|> curry APPLY <$> "(" >-- exp <*> many exp --< ")"
) tokens

and letx kind bs exp = letDups kind bs >>=+ (fn bs => LETX (kind, bs, exp))
and letrec _ _ = ERROR  "letrec is not included in Typed uScheme"
and bindings ts = ("(" >-- (many binding --< ")" <?> "(x e)...")) ts
and binding  ts = ("(" >-- (pair <$> name <*> exp --< ")" <?>
                                                        "(x e) in bindings")) ts

and badTyKeyword (loc, bad) =
      errorAt ("looking for expression but found `" ^ bad ^ "'") loc

and sexp tokens = (
     SYM          <$> (notDot <$>! name)
 <|> NUM          <$> int
 <|> BOOL         <$> booltok
 <|> (fn v => embedList [SYM "quote", v]) <$> (quote *> sexp)
 <|> embedList    <$> "(" >-- many sexp --< ")"
) tokens
and notDot "." = ERROR
                      "this interpreter cannot handle . in quoted S-expressions"
  | notDot s   = OK s


(* parsing for {\tuscheme} 686a *)
fun define tau f formals body =
  nodupsty ("formal parameter", "definition of function " ^ f) formals >>=+ (fn
                                                                          xts =>
  DEFINE (f, tau, (xts, body)))

fun valrec tau x e = VALREC (x, tau, e)

val def = 
     bracket "define" "(define type f (args) body)"
                                     (define <$> ty <*> name <*> @@ lformals
                                                                       <*>! exp)
 <|> bracket "val"    "(val x e)"              (curry VAL <$> name <*> exp)
 <|> bracket "val-rec" "(val-rec type x e)"    (valrec <$> ty <*> name <*> exp)
 <|> bracket "use"    "(use filename)"         (USE       <$> name)
 <|> literal ")" <!> "unexpected right parenthesis"
 <|> EXP <$> exp
 <?> "definition"
(* parsing for {\tuscheme} 686b *)
val tuschemeSyntax = (schemeToken, def)


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
(*   CHECKING AND EVALUATION FOR {\TUSCHEME}                     *)
(*                                                               *)
(*****************************************************************)

(* checking and evaluation for {\tuscheme} 267c *)
val unitVal = NIL
(* type declarations for consistency checking *)
val _ = op unitVal : value
(* checking and evaluation for {\tuscheme} 273a *)
exception BugInTypeChecking of string
(* evaluation for {\tuscheme} 686c *)
fun eval (e, rho) =
  let fun ev (LITERAL n) = n
        (* alternatives for [[ev]] for [[TYAPPLY]] and [[TYLAMBDA]] 272b *)
        | ev (TYAPPLY  (e, _)) = ev e
        | ev (TYLAMBDA (_, e)) = ev e
        (* more alternatives for [[ev]] for {\tuscheme} 686d *)
        | ev (VAR v) = !(find (v, rho))
        | ev (SET (n, e)) = 
            let val v = ev e
            in  find (n, rho) := v;
                v
            end
        (* more alternatives for [[ev]] for {\tuscheme} 687a *)
        | ev (IFX (e1, e2, e3)) = ev (if bool (ev e1) then e2 else e3)
        | ev (WHILEX (guard, body)) = 
            if bool (ev guard) then 
              (ev body; ev (WHILEX (guard, body)))
            else
              unitVal
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, unitVal)
            end
        (* more alternatives for [[ev]] for {\tuscheme} 687b *)
        | ev (LAMBDA (args, body)) = CLOSURE ((map (fn (n, ty) => n) args, body)
                                                                          , rho)
        (* more alternatives for [[ev]] for {\tuscheme} 687c *)
        | ev (APPLY (f, args))  = 
               (case ev f
                  of PRIMITIVE prim => prim (map ev args)
                   | CLOSURE clo => (* apply closure [[clo]] to [[args]] ((
                                                              mlscheme)) 218c *)
                                    let val ((formals, body), savedrho) = clo
                                        val actuals = map ev args
                                    in  eval (body, bindList (formals, map ref
                                                             actuals, savedrho))
                                        handle BindListLength => 
                                            raise RuntimeError (
                                      "Wrong number of arguments to closure; " ^
                                                                "expected (" ^
                                                         spaceSep formals ^ ")")
                                    end
                   | v => raise BugInTypeChecking "applied non-function"
               )
        (* more alternatives for [[ev]] for {\tuscheme} 687d *)
        | ev (LETX (LET, bs, body)) =
            let val (names, values) = ListPair.unzip bs
            in  eval (body, bindList (names, map (ref o ev) values, rho))
            end
        | ev (LETX (LETSTAR, bs, body)) =
            let fun step ((n, e), rho) = bind (n, ref (eval (e, rho)), rho)
            in  eval (body, foldl step rho bs)
            end
(* type declarations for consistency checking *)
val _ = op tyvar : string parser
val _ = op ty    : tyex   parser
(* type declarations for consistency checking *)
val _ = op eval : exp * value ref env -> value
val _ = op ev   : exp                 -> value
  in  ev e
  end
(* evaluation for {\tuscheme} 688a *)
fun evaldef (d, rho) =
  case d
    of VAL    (name, e)      =>
          let val v   = eval (e, rho)
              val rho = bind (name, ref v, rho)
          in  (rho, showVal name v)
          end
     | VALREC (name, tau, e) => 
          let val rho = bind (name, ref NIL, rho)
              val v   = eval (e, rho)
          in  find (name, rho) := v;
              (rho, showVal name v)
          end
     | EXP e => (* differs from VAL ("it", e) only in what it prints *)
          let val v   = eval (e, rho)
              val rho = bind ("it", ref v, rho)
          in  (rho, valueString v)
          end
     | DEFINE (name, tau, lambda) => evaldef (VALREC (name, tau, LAMBDA lambda),
                                                                            rho)
     | USE filename => raise RuntimeError
                                       "internal error -- `use' reached evaldef"
(* evaluation for {\tuscheme} 688b *)
and showVal name v =
      case v
        of CLOSURE   _ => name
         | PRIMITIVE _ => name
         | _ => valueString v
(* type declarations for consistency checking *)
val _ = op evaldef : def * value ref env -> value ref env * string
(* evaluation for {\tuscheme} 688c *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* type declarations for consistency checking *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* evaluation for {\tuscheme} 689a *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
val arithtype = funtype ([inttype, inttype], inttype)
(* type declarations for consistency checking *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
val _ = op arithtype : tyex
(* evaluation for {\tuscheme} 689c *)
fun embedPredicate f args = BOOL (f args)
fun comparison f = binaryOp (embedPredicate f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")
val comptype = funtype ([inttype, inttype], booltype)
(* type declarations for consistency checking *)
val _ = op comparison : (value * value -> bool) -> (value list -> value)
val _ = op intcompare : (int   * int   -> bool) -> (value list -> value)
val _ = op comptype   : tyex
type env_bundle = kind env * tyex env * value ref env
fun checkThenEval (d, envs as (delta, gamma, rho), echo) =
  case d
    of USE filename => use readCheckEvalPrint tuschemeSyntax filename envs
     | _ =>
        let val (gamma, tystring)  = elabdef (d, gamma, delta)
            val (rho,   valstring) = evaldef (d, rho)
            val _ = if size valstring > 0 then echo (valstring ^ " : " ^
                                                                       tystring)
                    else ()
(* type declarations for consistency checking *)
val _ = op checkThenEval : def * env_bundle * (string->unit) -> env_bundle
        in  (delta, gamma, rho)
        end
(* checking and evaluation for {\tuscheme} 273b *)
and readCheckEvalPrint (defs, echo, errmsg) envs =
  let fun processDef (def, envs) =
            let fun continue msg = (errmsg msg; envs)
            in  checkThenEval (def, envs, echo)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* more read-eval-print handlers 274a *)
                | TypeError         msg => continue ("type error: " ^ msg)
                | BugInTypeChecking msg => continue ("bug in type checking: " ^
                                                                            msg)
                (* more read-eval-print handlers 222c *)
                (* more read-eval-print handlers 223a *)
                | Div               => continue "Division by zero"
                | Overflow          => continue "Arithmetic overflow"
                | RuntimeError msg  => continue ("run-time error: " ^ msg)
                | NotFound n        => continue ("variable " ^ n ^ " not found")
            end
  in  streamFold processDef envs defs
  end
(* type declarations for consistency checking *)
val _ = op readCheckEvalPrint : def stream * (string->unit) * (string->unit) ->
                                                        env_bundle -> env_bundle


(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION FOR {\TUSCHEME}                              *)
(*                                                               *)
(*****************************************************************)

(* initialization for {\tuscheme} 274b *)
val initialEnvs =
  let fun addPrim ((name, prim, funty), (types, values)) = 
        ( bind (name, funty, types)
        , bind (name, ref (PRIMITIVE prim), values)
        )
      val (types, values) = foldl addPrim (emptyEnv, emptyEnv)
                            ((* primitive functions for {\tuscheme}\ [[::]] 689b
                                                                              *)
                             ("+", arithOp op +,   arithtype) :: 
                             ("-", arithOp op -,   arithtype) :: 
                             ("*", arithOp op *,   arithtype) :: 
                             ("/", arithOp op div, arithtype) ::
                             (* primitive functions for {\tuscheme}\ [[::]] 689d
                                                                              *)
                             ("<", intcompare op <, comptype) :: 
                             (">", intcompare op >, comptype) ::
                             ("=", comparison (fn (NIL,     NIL    ) => true
                                                | (NUM  n1, NUM  n2) => n1 = n2
                                                | (SYM  v1, SYM  v2) => v1 = v2
                                                | (BOOL b1, BOOL b2) => b1 = b2
                                                |  _                 => false)
                                 , FORALL (["'a"], funtype ([tyvarA, tyvarA],
                                                                  booltype))) ::
                             (* primitive functions for {\tuscheme}\ [[::]] 689e
                                                                              *)
                             ("null?", unaryOp (embedPredicate (fn (NIL   ) =>
                                                             true | _ => false))
                                 , FORALL (["'a"], funtype ([listtype tyvarA],
                                                                  booltype))) ::
                             ("cons", binaryOp (fn (a, b) => PAIR (a, b))
                                 , FORALL (["'a"], funtype ([tyvarA, listtype
                                                  tyvarA], listtype tyvarA))) ::
                             ("car",  unaryOp  (fn (PAIR (car, _)) => car 
                                                 | v => raise RuntimeError
                                                                (
                                    "car applied to non-list " ^ valueString v))
                                 , FORALL (["'a"], funtype ([listtype tyvarA],
                                                                    tyvarA))) ::
                             ("cdr",  unaryOp  (fn (PAIR (_, cdr)) => cdr 
                                                 | v => raise RuntimeError
                                                                (
                                    "cdr applied to non-list " ^ valueString v))
                                 , FORALL (["'a"], funtype ([listtype tyvarA],
                                                           listtype tyvarA))) ::
                             (* primitive functions for {\tuscheme}\ [[::]] 690a
                                                                              *)
                             ("print", unaryOp (fn x => (print (valueString x^
                                                               "\n"); unitVal)),
                                 FORALL (["'a"], funtype ([tyvarA], unittype)))
                                                                         :: nil)
      fun addVal ((name, v, ty), (types, values)) = 
        ( bind (name, ty, types)
        , bind (name, ref v, values)
        )
      val (types, values) = foldl addVal (types, values)
                            ((* primitives that aren't functions, for {\tuscheme
                                                               }\ [[::]] 690b *)
                             (* if this space is completely empty, something
                                       goes wrong with the software OMIT *) nil)
      fun addKind ((name, kind), kinds) = bind (name, kind, kinds)
      val kinds   = foldl addKind emptyEnv
                    ((* primitive type constructors for {\tuscheme}\ [[::]] 258b
                                                                              *)
                     ("int",      TYPE) ::
                     ("bool",     TYPE) ::
                     ("sym",      TYPE) ::
                     ("unit",     TYPE) ::
                     ("list",     ARROW ([TYPE],       TYPE)) ::
                     ("function", ARROW ([TYPE, TYPE], TYPE)) :: nil)
      val envs    = (kinds, types, values)
      val basis   = (* ML representation of initial basis (generated by a script
                                                                            ) *)

                     [
   "(val list1 (type-lambda ('a) (lambda (('a x)) ((@ cons 'a) x (@ '() 'a)))))"
                     , "(val list2 (type-lambda ('a) (lambda (('a x) ('a y))"
                     ,
            "                               ((@ cons 'a) x ((@ list1 'a) y)))))"
                     ,
                   "(val list3 (type-lambda ('a) (lambda (('a x) ('a y) ('a z))"
                     ,
          "                               ((@ cons 'a) x ((@ list2 'a) y z)))))"
                     , "(val o (type-lambda ('a 'b 'c) "
                     , "  (lambda (((function ('b) 'c) f)"
                     , "           ((function ('a) 'b) g))"
                     , "     (lambda (('a x)) (f (g x))))))"
                     , ""
                     , "(val curry (type-lambda ('a 'b 'c)"
                     , "   (lambda (((function ('a 'b) 'c) f)) "
                     , "      (lambda (('a x)) (lambda (('b y)) (f x y))))))"
                     , ""
                     , "(val uncurry (type-lambda ('a 'b 'c)"
                     , "   (lambda (((function ('a) (function ('b) 'c)) f))"
                     , "      (lambda (('a x) ('b y)) ((f x) y)))))"
                     , "(val-rec"
                     ,
                  "  (forall ('a) (function ((list 'a)) int))  ; type of length"
                     , "  length                                    ; name"
                     ,
    "  (type-lambda ('a)                         ; value : polymorphic function"
                     , "     (lambda (((list 'a) l))"
                     , "       (if ((@ null? 'a) l) 0"
                     , "          (+ 1 ((@ length 'a) ((@ cdr 'a) l)))))))"
                     , "(val-rec "
                     ,
                    "  (forall ('a) (function ((list 'a) (list 'a)) (list 'a)))"
                     , "  revapp"
                     , "  (type-lambda ('a)"
                     , "     (lambda (((list 'a) xs)  ((list 'a) ys))"
                     , "        (if ((@ null? 'a) xs)"
                     , "        ys"
                     ,
  "        ((@ revapp 'a) ((@ cdr 'a) xs) ((@ cons 'a) ((@ car 'a) xs) ys))))))"
                     , "(val caar"
                     , "   (type-lambda ('a)"
                     , "      (lambda (((list (list 'a)) l))"
                     , "          ((@ car 'a) ((@ car (list 'a)) l)))))"
                     , "(val cadr"
                     , "   (type-lambda ('a)"
                     , "      (lambda (((list (list 'a)) l))"
                     , "          ((@ car (list 'a)) ((@ cdr (list 'a)) l)))))"
                     , "(define bool and ((bool b) (bool c)) (if b  c  b))"
                     , "(define bool or  ((bool b) (bool c)) (if b  b  c))"
                     , "(define bool not ((bool b))          (if b #f #t))"
                     ,
      "(val-rec (forall ('a) (function ((list 'a) (list 'a)) (list 'a))) append"
                     , "  (type-lambda ('a)"
                     , "     (lambda (((list 'a) xs)  ((list 'a) ys))"
                     , "       (if ((@ null? 'a) xs)"
                     , "         ys"
                     ,
 "         ((@ cons 'a) ((@ car 'a) xs) ((@ append 'a) ((@ cdr 'a) xs) ys))))))"
                     ,
"(val-rec (forall ('a) (function ((function ('a) bool) (list 'a)) (list 'a))) filter"
                     , "   (type-lambda ('a)"
                     ,
                      "      (lambda (((function ('a) bool) p?)  ((list 'a) l))"
                     , "         (if ((@ null? 'a) l)"
                     , "             (@ '() 'a)"
                     , "             (if (p? ((@ car 'a) l))"
                     ,
"                 ((@ cons 'a) ((@ car 'a) l) ((@ filter 'a) p? ((@ cdr 'a) l)))"
                     , "                 ((@ filter 'a) p? ((@ cdr 'a) l)))))))"
                     , "; missing exists?"
                     , "; missing all?"
                     ,
"(val-rec (forall ('a 'b) (function ((function ('a) 'b) (list 'a)) (list 'b))) map"
                     , "   (type-lambda ('a 'b)"
                     , "      (lambda (((function ('a) 'b) f)  ((list 'a) l))"
                     , "         (if ((@ null? 'a) l)"
                     , "             (@ '() 'b)"
                     ,
"             ((@ cons 'b) (f ((@ car 'a) l)) ((@ map 'a 'b) f ((@ cdr 'a) l)))))))"
                     , "(define bool <= ((int x) (int y)) (not (> x y)))"
                     , "(define bool >= ((int x) (int y)) (not (< x y)))"
                     ,
     "(val != (type-lambda ('a) (lambda (('a x) ('a y)) (not ((@ = 'a) x y)))))"
                     , "(define int max ((int x) (int y)) (if (> x y) x y))"
                     , "(define int min ((int x) (int y)) (if (< x y) x y))"
                     , ""
                     , "(define int mod ((int m) (int n)) (- m (* n (/ m n))))"
                     ,
   "(define int gcd ((int m) (int n)) (if ((@ = int) n 0) m (gcd n (mod m n))))"
                     ,
                      "(define int lcm ((int m) (int n)) (* m (/ n (gcd m n))))"
                      ]
(* type declarations for consistency checking *)
val _ = op kinds  : kind      env
val _ = op types  : tyex      env
val _ = op values : value ref env
val _ = op envs   : env_bundle
      val defs  = reader tuschemeSyntax noPrompts ("initial basis", streamOfList
                                                                          basis)
  in  readCheckEvalPrint (defs, fn _ => (), fn _ => ()) envs
  end
(* initialization for {\tuscheme} 274c *)
fun runInterpreter noisy = 
  let fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader tuschemeSyntax prompts ("standard input", streamOfLines
                                                                   TextIO.stdIn)
  in  ignore (readCheckEvalPrint (defs, writeln, errorln) initialEnvs)
  end 


(*****************************************************************)
(*                                                               *)
(*   COMMAND LINE                                                *)
(*                                                               *)
(*****************************************************************)

(* command line 223d *)
fun main ["-q"] = runInterpreter false
  | main []     = runInterpreter true
  | main _      =
      TextIO.output (TextIO.stdErr, "Usage: " ^ CommandLine.name () ^ " [-q]\n")
val _ = main (CommandLine.arguments ())
