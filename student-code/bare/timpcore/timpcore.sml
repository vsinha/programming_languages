(* timpcore.sml 247d *)


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
exception LeftAsExercise of string


(*****************************************************************)
(*                                                               *)
(*   TYPES FOR \TIMPCORE                                         *)
(*                                                               *)
(*****************************************************************)

(* types for \timpcore 235c *)
datatype ty    = INTTY | BOOLTY | UNITTY | ARRAYTY of ty
datatype funty = FUNTY of ty list * ty
(* types for \timpcore 235d *)
(* printing types for \timpcore 677a *)
fun typeString BOOLTY        = "bool"
  | typeString INTTY         = "int"
  | typeString UNITTY        = "unit"
  | typeString (ARRAYTY tau) = "(array " ^ typeString tau ^ ")"
(* types for \timpcore 235e *)
fun eqType (INTTY,      INTTY)  = true
  | eqType (BOOLTY,     BOOLTY) = true
  | eqType (UNITTY,     UNITTY) = true
  | eqType (ARRAYTY t1, ARRAYTY t2) = eqType (t1, t2)
  | eqType (_,          _)      = false
and eqTypes ([],      [])      = true
  | eqTypes (t1::ts1, t2::ts2) = eqType (t1, t2) andalso eqTypes (ts1, ts2)
  | eqTypes (_,       _)       = false


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
(*   ABSTRACT SYNTAX AND VALUES FOR \TIMPCORE                    *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values for \timpcore 235f *)
datatype value = NUM   of int
               | ARRAY of value array
(* abstract syntax and values for \timpcore 236a *)
datatype exp   = LITERAL of value
               | VAR     of name
               | SET     of name * exp
               | IFX     of exp * exp * exp
               | WHILEX  of exp * exp
               | BEGIN   of exp list
               | EQ      of exp * exp
               | PRINT   of exp
               | APPLY   of name * exp list
               (* array extensions to \timpcore's abstract syntax 249c *)
               | AGET  of exp * exp
               | ASET  of exp * exp * exp
               | AMAKE of exp * exp
               | ALEN  of exp
(* abstract syntax and values for \timpcore 236b *)
type userfun = { formals : (name * ty) list, body : exp, returns : ty }
datatype def = VAL    of name * exp
             | EXP    of exp
             | DEFINE of name * userfun
             | USE    of name
(* abstract syntax and values for \timpcore 236c *)
datatype func = USERDEF   of string list * exp
              | PRIMITIVE of value list -> value
(* abstract syntax and values for \timpcore 236d *)
(* printing values for \timpcore 677b *)
fun valueString (NUM n) = Int.toString n
  | valueString (ARRAY a) =
      if Array.length a = 0 then
          "[]"
      else
          let val elts = Array.foldr (fn (v, s) => " " :: valueString v :: s) [
                                                                          "]"] a
          in  String.concat ("[" :: tl elts)
          end
(* type declarations for consistency checking *)
val _ = op typeString : ty -> string
(* type declarations for consistency checking *)
val _ = op eqType  : ty      * ty     -> bool
val _ = op eqTypes : ty list * ty list -> bool
(* type declarations for consistency checking *)
val _ = op valueString : value -> string
(* abstract syntax and values for \timpcore 250a *)
exception BugInTypeChecking of string
fun toArray (ARRAY a) = a
  | toArray _         = raise BugInTypeChecking "non-array value"
fun toInt   (NUM n)   = n
  | toInt _           = raise BugInTypeChecking "non-integer value"
(* type declarations for consistency checking *)
val _ = op toArray : value -> value array
val _ = op toInt   : value -> int


(*****************************************************************)
(*                                                               *)
(*   PARSING FOR \TIMPCORE                                       *)
(*                                                               *)
(*****************************************************************)

(* parsing for \timpcore 678 *)
val name    = (fn (NAME  n) => SOME n  | _ => NONE) <$>? token
val booltok = (fn (SHARP b) => SOME b  | _ => NONE) <$>? token
val int     = (fn (INT   n) => SOME n  | _ => NONE) <$>? token
val quote   = (fn (QUOTE)   => SOME () | _ => NONE) <$>? token

fun exp tokens = (
     VAR <$> name
 <|> (LITERAL o NUM) <$> int
 <|> booltok <!> "Typed Impcore has no Boolean literals"
 <|> quote   <!> "Typed Impcore has no quoted literals"
 <|> bracket "if"     "(if e1 e2 e3)"            (curry3 IFX    <$> exp <*> exp
                                                                        <*> exp)
 <|> bracket "while"  "(while e1 e2)"            (curry  WHILEX <$> exp <*> exp)
 <|> bracket "set"    "(set x e)"                (curry  SET    <$> name <*> exp
                                                                               )
 <|> bracket "begin"  ""                         (       BEGIN <$> many exp)
 <|> bracket "print"  "(print e)"                (       PRINT <$> exp)
 <|> bracket "="      "(= e1 e2)"                (curry  EQ    <$> exp <*> exp)
 <|> bracket "array-get"    "(array-get a i)"    (curry  AGET  <$> exp <*> exp)

 <|> bracket "array-set"    "(array-set a i e)"  (curry3 ASET  <$> exp <*> exp
                                                                        <*> exp)
 <|> bracket "array-make"   "(array-make n e)"   (curry  AMAKE <$> exp <*> exp)
 <|> bracket "array-length" "(array-length a)"   (       ALEN  <$> exp)

 <|> "(" >-- literal ")" <!> "empty application"
 <|> curry APPLY <$> "(" >-- impcorefun <*> many exp --< ")"
) tokens
and impcorefun tokens = 
  (   name 
  <|> exp <!> "only named functions can be applied"
  <?> "function name"
  ) tokens
(* parsing for \timpcore 679a *)
fun ty tokens = (
     BOOLTY <$ literal "bool"
 <|> UNITTY <$ literal "unit"
 <|> INTTY  <$ literal "int"
 <|> (fn (loc, n) => errorAt ("Cannot recognize name " ^ n ^ " as a type") loc)
     <$>! @@ name 
 <|> bracket "array" "(array ty)" (ARRAYTY <$> ty)
 <?> "int, bool, unit, or (array ty)"
 ) tokens

val formal  = "(" >-- ((fn tau => fn x => (x, tau)) <$> ty <*> name --< ")"
                      <?> "(ty argname)")
val formals = "(" >-- many formal --< ")" <?> "((ty1 x1) ... (tyN xN))"

fun define ty f formals body =
      defineDups f formals >>=+ (fn formals =>
      DEFINE (f, { returns = ty, formals = formals, body = body }))
and defineDups f = nodupsty ("formal parameter", "definition of function " ^ f) 
and nodupsty what (loc, xts) = 
      nodups what (loc, map fst xts) >>=+ (fn _ => xts)
                                          (* error on duplicate names *)
val def = 
     bracket "define" "(define ty f (args) body)" 
                                     (define <$> ty <*> name <*> @@ formals <*>!
                                                                            exp)
 <|> bracket "val"    "(val x e)"        (curry VAL <$> name <*> exp)
 <|> bracket "use"    "(use filename)"   (USE <$> name)
 <|> literal ")" <!> "unexpected right parenthesis"
 <|> EXP <$> exp
 <?> "definition"
(* parsing for \timpcore 679b *)
val timpcoreSyntax = (schemeToken, def)


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
(*   TYPE CHECKING FOR \TIMPCORE                                 *)
(*                                                               *)
(*****************************************************************)

(* type checking for \timpcore 241a *)
exception TypeError of string
fun typeof (e, globals, functions, formals) =
  let (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           1b *)
      fun ty (LITERAL v) = INTTY
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           1c *)
        | ty (VAR x)     = (find (x, formals) handle NotFound _ => find (x,
                                                                       globals))
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           2a *)
        | ty (SET (x, e)) =
               let val tau_x = ty (VAR x)
                   val tau_e = ty e
               in  if eqType (tau_x, tau_e) then
                     tau_x
                   else
                     raise TypeError ("Set variable " ^ x ^ " of type " ^
                                                              typeString tau_x ^
                                      " to value of type " ^ typeString tau_e)
               end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           2b *)
        | ty (IFX (e1, e2, e3)) =
            let val tau1 = ty e1
                val tau2 = ty e2
                val tau3 = ty e3
            in  if eqType (tau1, BOOLTY) then
                  if eqType (tau2, tau3) then
                    tau2
                  else
                    raise TypeError ("In if expression, true branch has type " ^
                                     typeString tau2 ^
                                                 " but false branch has type " ^
                                     typeString tau3)
                else
                  raise TypeError ("Condition in if expression has type " ^
                                                               typeString tau1 ^
                                   ", which should be " ^ typeString BOOLTY)
            end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           3a *)
        | ty (WHILEX (e1, e2)) =
            let val tau1 = ty e1
                val tau2 = ty e2
            in  if eqType (tau1, BOOLTY) then
                  UNITTY
                else
                  raise TypeError ("Condition in while expression has type " ^
                                   typeString tau1 ^ ", which should be " ^
                                   typeString BOOLTY)
            end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           3b *)
        | ty (BEGIN es) =
             let val bodytypes = map ty es
                 fun last tau []     = tau
                   | last tau (h::t) = last h t
             in  last UNITTY bodytypes
             end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           3c *)
        | ty (EQ (e1, e2)) =
             let val (tau1, tau2) = (ty e1, ty e2)
             in  if eqType (tau1, tau2) then
                   BOOLTY
                 else
                   raise TypeError (
                                "Equality compares values of different types " ^
                                    typeString tau1 ^ " and " ^ typeString tau2)
             end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           4a *)
        | ty (PRINT e) = (ty e; UNITTY)
      (* function [[ty]], to check the type of an expression, given $\itenvs$ 24
                                                                           4b *)
        | ty (APPLY (f, actuals)) =
             let val actualtypes                     = map ty actuals
                 val FUNTY (formaltypes, resulttype) = find (f, functions)
                 (* definition of [[parameterError]] 244c *)
                 fun parameterError (n, atau::actuals, ftau::formals) =
                       if eqType (atau, ftau) then
                         parameterError (n+1, actuals, formals)
                       else
                         raise TypeError ("In call to " ^ f ^ ", parameter " ^
                                          Int.toString n ^ " has type " ^
                                                               typeString atau ^
                                          " where type " ^ typeString ftau ^
                                                                 " is expected")
                   | parameterError _ =
                       raise TypeError ("Function " ^ f ^ " expects " ^
                                        Int.toString (length formaltypes) ^
                                                                " parameters " ^
                                        "but got " ^ Int.toString (length
                                                                   actualtypes))
                 (* type declarations for consistency checking *)
                 val _ = op parameterError : int * ty list * ty list -> 'a
             in  if eqTypes (actualtypes, formaltypes) then
                   resulttype
                 else
                   parameterError (1, actualtypes, formaltypes)
             end
      (* function [[ty]], to check the type of an expression, given $\itenvs$ ((
                                                              prototype)) 251 *)
      | ty (AGET (a, i))       = raise LeftAsExercise "AGET"
      | ty (ASET (a, i, e))    = raise LeftAsExercise "ASET"
      | ty (AMAKE (len, init)) = raise LeftAsExercise "AMAKE"
      | ty (ALEN a)            = raise LeftAsExercise "ALEN"
(* type declarations for consistency checking *)
val _ = op typeof  : exp * ty env * funty env * ty env -> ty
val _ = op ty      : exp -> ty
  in  ty e
  end
(* type checking for \timpcore 244d *)
exception RuntimeError of string
fun elabdef (d, globals, functions) =
    case d
      of (* cases for elaborating definitions in \timpcore 245a *)
           VAL (x, e) => (bind (x, typeof (e, globals, functions, emptyEnv),
                                                            globals), functions)
         (* cases for elaborating definitions in \timpcore 245b *)
         | EXP e => elabdef (VAL ("it", e), globals, functions)
         (* cases for elaborating definitions in \timpcore 245c *)
         | DEFINE (name, {returns, formals, body}) =>
            let val (fnames, ftys) = ListPair.unzip formals
                val functions' = bind (name, FUNTY (ftys, returns), functions)
                val tau = typeof (body, globals, functions', bindList (fnames,
                                                                ftys, emptyEnv))
            in  if eqType (tau, returns) then
                  (globals, functions')
                else
                  raise TypeError ("Body of function has type " ^ typeString tau
                                                                               ^
                                   ", which does not match declaration of " ^
                                   typeString returns)
            end
         (* cases for elaborating definitions in \timpcore 245d *)
         | USE _ => raise BugInTypeChecking "`use' reached the type checker"
(* type declarations for consistency checking *)
val _ = op elabdef : def * ty env * funty env -> ty env * funty env


(*****************************************************************)
(*                                                               *)
(*   CHECKING AND EVALUATION FOR \TIMPCORE                       *)
(*                                                               *)
(*****************************************************************)

(* checking and evaluation for \timpcore 246a *)
(* evaluation for \timpcore 681a *)
(* definition of [[eval]] for \timpcore 680a *)
fun eval (e, globals, functions, formals) =
  let fun toBool (NUM 0) = false
        | toBool _       = true
      fun ofBool true    = NUM 1
        | ofBool false   = NUM 0
      val unitVal = NUM 1983 (* all values of unit type must test equal with =
                                                                              *)
      fun eq (NUM n1,   NUM n2)   = (n1 = n2)
        | eq (ARRAY a1, ARRAY a2) = (a1 = a2)
        | eq _                    = false
      fun findVar v = find (v, formals) handle NotFound _ => find (v, globals)
      fun ev (LITERAL n)          = n
        | ev (VAR x)              = !(findVar x)
        | ev (SET (x, e))         = let val v = ev e in v before findVar x := v
                                                                             end
        | ev (IFX (cond, t, f))   = if toBool (ev cond) then ev t else ev f
        | ev (WHILEX (cond, exp)) =
            if toBool (ev cond) then
                (ev exp; ev (WHILEX (cond, exp)))
            else
                unitVal
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, unitVal)
            end
        | ev (EQ (e1, e2)) = ofBool (eq (ev e1, ev e2))
        | ev (PRINT e)     = (print (valueString (ev e)^"\n"); unitVal)
        | ev (APPLY (f, args)) =
            (case find (f, functions)
               of PRIMITIVE p  => p (map ev args)
                | USERDEF func => (* apply user-defined function [[func]] to
                                                                [[args]] 680b *)
                                  let val (formals, body) = func
                                      val actuals         = map (ref o ev) args
                                  (* type declarations for consistency checking
                                                                              *)
                                  val _ = op formals : name      list
                                  val _ = op actuals : value ref list
                                  in  eval (body, globals, functions, bindList (
                                                    formals, actuals, emptyEnv))
                                      handle BindListLength => 
                                          raise BugInTypeChecking
                                         "Wrong number of arguments to function"
                                  end)
        (* more alternatives for [[ev]] for \timpcore 250b *)
        | ev (AGET (a, i)) =
            (Array.sub (toArray (ev a), toInt (ev i))
             handle Subscript => raise RuntimeError
                                                "Array subscript out of bounds")
        | ev (ASET (e1, e2, e3)) =
            (let val (a, i, v) = (ev e1, ev e2, ev e3)
             in  Array.update (toArray a, toInt i, v);
                 v
             end handle Subscript => raise RuntimeError
                                                "Array subscript out of bounds")
        | ev (AMAKE (len, init)) = 
             (ARRAY (Array.array (toInt (ev len), ev init))
              handle Size => raise RuntimeError
                                         "array length too large (or negative)")
        | ev (ALEN a) = NUM (Array.length (toArray (ev a)))
        (* type declarations for consistency checking *)
        val _ = op ev : exp -> value
(* type declarations for consistency checking *)
val _ = op ev : exp -> value
  in  ev e
  end
(* type declarations for consistency checking *)
val _ = op eval : exp * value ref env * func env * value ref env -> value
(* evaluation for \timpcore 681b *)
fun evaldef (d, globals, functions, echo) =
  case d
    of VAL (name, e) => (* evaluate [[e]] and bind to [[name]] 681c *)
                        let val v = eval (e, globals, functions, emptyEnv)
                            val _ = echo (valueString v)
                        in  (bind (name, ref v, globals), functions)
                        end
     | EXP e => evaldef (VAL ("it", e), globals, functions, echo)
     | DEFINE (f, {body=e, formals=xs, returns=rt}) =>
          (globals, bind (f, USERDEF (map #1 xs, e), functions))
          before echo f
     | USE _ => raise RuntimeError "Internal error - `use' was evaluated"
(* evaluation for \timpcore 681d *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* type declarations for consistency checking *)
val _ = op evaldef : def * value ref env * func env * (string->unit) -> value
                                                              ref env * func env
(* type declarations for consistency checking *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* evaluation for \timpcore 681e *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
val arithtype = FUNTY ([INTTY, INTTY], INTTY)
(* type declarations for consistency checking *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
val _ = op arithtype : funty
(* evaluation for \timpcore 682a *)
fun embedPredicate f args = NUM (if f args then 1 else 0)
fun comparison f = binaryOp (embedPredicate f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")
val comptype = FUNTY ([INTTY, INTTY], BOOLTY)
(* type declarations for consistency checking *)
val _ = op comparison : (value * value -> bool) -> (value list -> value)
val _ = op intcompare : (int   * int   -> bool) -> (value list -> value)
val _ = op comptype   : funty
type env_bundle = ty env * funty env * value ref env * func env
fun checkThenEval (d, envs as (tglobals, tfuns, vglobals, vfuns), echo) =
  case d
    of USE filename => use readCheckEvalPrint timpcoreSyntax filename envs
     | _ =>
        let val (tglobals, tfuns) = elabdef (d, tglobals, tfuns)
            val (vglobals, vfuns) = evaldef (d, vglobals, vfuns, echo)
(* type declarations for consistency checking *)
val _ = op checkThenEval : def * env_bundle * (string->unit) -> env_bundle
        in  (tglobals, tfuns, vglobals, vfuns)
        end
(* checking and evaluation for \timpcore 246b *)
and readCheckEvalPrint (defs, echo, errmsg) envs =
  let fun processDef (def, envs) =
            let fun continue msg = (errmsg msg; envs)
            in  checkThenEval (def, envs, echo)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* more read-eval-print handlers 247a *)
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
(*   INITIALIZATION FOR \TIMPCORE                                *)
(*                                                               *)
(*****************************************************************)

(* initialization for \timpcore 247b *)
val initialEnvs =
  let fun addPrim ((name, prim, funty), (tfuns, vfuns)) = 
        ( bind (name, funty, tfuns)
        , bind (name, PRIMITIVE prim, vfuns)
        )
      val (tfuns, vfuns)  = foldl addPrim (emptyEnv, emptyEnv)
                            ((* primops for \timpcore\ [[::]] 681f *)
                             ("+", arithOp op +,   arithtype) :: 
                             ("-", arithOp op -,   arithtype) :: 
                             ("*", arithOp op *,   arithtype) :: 
                             ("/", arithOp op div, arithtype) ::
                             (* primops for \timpcore\ [[::]] 682b *)
                             ("<", intcompare op <, comptype) :: 
                             (">", intcompare op >, comptype) :: nil)
      val envs  = (emptyEnv, tfuns, emptyEnv, vfuns)
      val basis = (* ML representation of initial basis (generated by a script)
                                                                              *)

                   [ "(define bool and ((bool b) (bool c)) (if b c b))"
                   , "(define bool or  ((bool b) (bool c)) (if b b c))"
                   ,
                  "(define bool not ((bool b))          (if b (= 1 0) (= 0 0)))"
                   , "(define bool <= ((int x) (int y)) (not (> x y)))"
                   , "(define bool >= ((int x) (int y)) (not (< x y)))"
                   , "(define bool != ((int x) (int y)) (not (= x y)))"
                   , "(define int mod ((int m) (int n)) (- m (* n (/ m n))))"
                    ]
      val defs  = reader timpcoreSyntax noPrompts ("initial basis", streamOfList
                                                                          basis)
  in  readCheckEvalPrint (defs, fn _ => (), fn _ => ()) envs
  end
(* initialization for \timpcore 247c *)
fun runInterpreter noisy = 
  let fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader timpcoreSyntax prompts ("standard input", streamOfLines
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
