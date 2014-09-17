(* usm.sml 475a *)


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


(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS                                            *)
(*                                                               *)
(*****************************************************************)

(* lexical analysis ((usm)) 699a *)
type srcloc = string * int
val nullsrc = ("internally generated SEND node", 1)
fun srclocString (source, line) = source ^ ", line " ^ Int.toString line
(* lexical analysis ((usm)) 699b *)
datatype token = INT     of int
               | NAME    of name
               | BRACKET of char          (* ( or ) or [ or ] *)
               | SHARP   of string option (* symbol or array *)
(* lexical analysis ((usm)) 699c *)
fun tokenString (INT     n)      = Int.toString n
  | tokenString (NAME    x)      = x
  | tokenString (BRACKET c)      = str c
  | tokenString (SHARP NONE)     = "#"
  | tokenString (SHARP (SOME s)) = "#" ^ s
(* lexical analysis ((usm)) 699d *)
fun isLiteral s token = 
  case (s, token) of ("#", SHARP NONE) => true
                   | (s,   NAME s' )   => s = s'
                   | (s,   BRACKET c)  => s = str c
                   | _ => false
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
(* lexical analysis ((usm)) 700a *)
local
  val isDelim = fn c => isDelim c orelse c = #"[" orelse c = #"]"
  val nondelims = many1 (sat (not o isDelim) one)

  fun validate NONE = NONE (* end of line *)
    | validate (SOME (#";", cs)) = NONE (* comment *)
    | validate (SOME (c, cs)) = 
        let val msg = "invalid initial character in `" ^
                      implode (c::listOfStream cs) ^ "'"
        in  SOME (ERROR msg, EOS) : (token error * char stream) option
        end
in
  val smalltalkToken =
    whitespace *> (
            BRACKET                  <$> sat (Char.contains "()[]") one
        <|> (SHARP o SOME o implode) <$> (oneEq #"#" *> nondelims)
        <|> SHARP NONE               <$  oneEq #"#"                        
        <|> INT                      <$> intToken isDelim   
        <|> (NAME o implode)         <$> nondelims                          
        <|> (validate o streamGet)
        )
(* type declarations for consistency checking *)
val _ = op smalltalkToken : token lexer
end


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values ((usm)) 467a *)
datatype exp = VAR     of name
             | SET     of name * exp
             | SEND    of srcloc * name * exp * exp list
             | BEGIN   of exp list
             | BLOCK   of name list * exp list
             | LITERAL of rep
             | VALUE   of value
             | SUPER
(* abstract syntax and values ((usm)) 467b *)
and def
  = VAL    of name * exp
  | EXP    of exp
  | DEFINE of name * name list * exp
  | CLASSD of { name    : string
              , super   : string
              , ivars   : string list     (* instance variables *)
              , methods : (method_kind * name * method_impl) list
              }
  | USE of name
and method_kind = IMETHOD          (* instance method *)
                | CMETHOD          (* class method    *)
and method_impl = USER_IMPL of name list * name list * exp
                | PRIM_IMPL of name
(* abstract syntax and values ((usm)) 468a *)
and    rep = USER     of value ref env (* collection of named instance variables
                                                                              *)
           | ARRAY    of value Array.array
           | NUM      of int
           | SYM      of name
           | CLOSURE  of name list * exp list * value ref env * class
           | CLASSREP of class
(* abstract syntax and values ((usm)) 468b *)
and class  = CLASS of { name    : name            (* name of the class *)
                      , super   : class option    (* superclass, if any *)
                      , ivars   : string list     (* instance variables *)
                      , methods : method env      (* both exported and private
                                                                              *)
                      , id      : int             (* uniquely identifies class
                                                                              *)
                      }
(* abstract syntax and values ((usm)) 468c *)
and method
  = PRIM_METHOD of name * (value * value list -> value)
  | USER_METHOD of { name : name, formals : name list, locals : name list, body
                                                                           : exp
                   , superclass : class (* used to send messages to super *)
                   }
(* abstract syntax and values ((usm)) 468d *)
withtype value = class * rep
(* abstract syntax and values ((usm)) 469 *)
exception RuntimeError  of string (* error caused by user *)
exception InternalError of string (* bug in the interpreter *)
(* abstract syntax and values ((usm)) 475b *)
fun className (CLASS {name, ...}) = name
fun classId   (CLASS {id,   ...}) = id
(* type declarations for consistency checking *)
val _ = op className : class -> name
val _ = op classId   : class -> int
(* abstract syntax and values ((usm)) 476a *)
fun methodName (PRIM_METHOD (n, _)) = n
  | methodName (USER_METHOD { name, ... }) = name
fun renameMethod (n, PRIM_METHOD (_, f)) = PRIM_METHOD (n, f)
  | renameMethod _ = raise InternalError "renamed user method"
fun methods l = foldl (fn (m, rho) => bind (methodName m, m, rho)) emptyEnv l
(* type declarations for consistency checking *)
val _ = op methodName   : method -> name
val _ = op methods      : method list -> method env
val _ = op renameMethod : name * method -> method
(* abstract syntax and values ((usm)) 476b *)
local 
  val n = ref 10 (* new classes start here *)
  fun uid () = !n before n := !n + 1
in
  fun mkClass name super ivars ms =
    CLASS { name = name, super = SOME super, ivars = ivars, methods = methods ms
                                                                               ,
            id = uid () }
end
(* type declarations for consistency checking *)
val _ = op mkClass : name -> class -> name list -> method list -> class


(*****************************************************************)
(*                                                               *)
(*   BOOTSTRAPPING SUPPORT                                       *)
(*                                                               *)
(*****************************************************************)

(* bootstrapping support 476c *)
local 
  val intClass    = ref NONE : class option ref
  val symbolClass = ref NONE : class option ref
  val arrayClass  = ref NONE : class option ref
  fun badlit what = 
    raise InternalError
        ("(bootstrapping) -- cannot " ^ what ^ " anywhere in initial basis")
in
  fun mkInteger n = (valOf (!intClass), NUM n)
    handle Option => badlit "evaluate integer literal or use array literal"
  
  fun mkSymbol s = (valOf (!symbolClass), SYM s)
    handle Option => badlit "evaluate symbol literal or use array literal"
  
  fun mkArray a = (valOf (!arrayClass), ARRAY (Array.fromList a))
    handle Option => badlit "use array literal"
(* type declarations for consistency checking *)
val _ = op mkInteger : int        -> value
val _ = op mkSymbol  : string     -> value
val _ = op mkArray   : value list -> value
(* bootstrapping support 477a *)
  fun findInitialClass (name, xi) =
        case !(find (name, xi))
          of (_, CLASSREP c) => c
           | _ => raise InternalError (name ^
                                         " is not a class in the initial basis")
  fun closeLiteralsCycle xi =
    ( intClass    := SOME (findInitialClass ("SmallInteger", xi))
    ; symbolClass := SOME (findInitialClass ("Symbol",       xi))
    ; arrayClass  := SOME (findInitialClass ("Array",        xi))
    )
end
(* type declarations for consistency checking *)
val _ = op findInitialClass : string * value ref env -> class
(* bootstrapping support 477b *)
local
  val trueValue  = ref NONE : value option ref
  val falseValue = ref NONE : value option ref
in
  fun mkBoolean b = valOf (!(if b then trueValue else falseValue))
    handle Option => 
        raise InternalError 
            "Bad booleanClass; evaluated boolean expression in initial basis?"
  fun closeBooleansCycle xi =
    ( trueValue  := SOME (!(find ("true",  xi)))
    ; falseValue := SOME (!(find ("false", xi)))
    )
end
(* type declarations for consistency checking *)
val _ = op mkBoolean : bool -> value
(* bootstrapping support 478a *)
local
  val blockClass = ref NONE : class option ref
in
  fun mkBlock c = (valOf (!blockClass), CLOSURE c)
    handle Option => 
        raise InternalError 
            "Bad blockClass; evaluated block expression in initial basis?"
  fun closeBlocksCycle xi =
    blockClass := SOME (findInitialClass ("Block", xi))
end
(* type declarations for consistency checking *)
val _ = op mkBlock : name list * exp list * value ref env * class -> value


(*****************************************************************)
(*                                                               *)
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* parsing ((usm)) 700b *)
val blockDups         = nodups ("formal parameter",  "block")
fun methodDups kind f = nodups ("formal parameter",   kind ^ " " ^ f)
fun localDups  kind f = nodups ("local variable",     kind ^ " " ^ f)
fun ivarDups c        = nodups ("instance variable", "class " ^ c)
(* parsing ((usm)) 701 *)
fun arity "if"    = 2
  | arity "while" = 1
  | arity name =
      let val cs = explode name
      in  if Char.isAlpha (hd cs) then
            length (List.filter (fn c => c = #":") cs)
          else
            1
      end

fun arityOk "value" _ = true
  | arityOk name args = arity name = length args

fun arityErrorAt loc what msgname args =
  let fun argn n = if n = 1 then "1 argument" else Int.toString n ^ " arguments"
  in  errorAt ("in " ^ what ^ ", message " ^ msgname ^ " expects " ^
                         argn (arity msgname) ^ ", but gets " ^
                         argn (length args)) loc
  end
(* parsing ((usm)) 702 *)
val name = (fn (NAME s)         => SOME s | _ => NONE) <$>? token
val int  = (fn (INT n)          => SOME n | _ => NONE) <$>? token
val sym  = (fn (SHARP (SOME s)) => SOME s | _ => NONE) <$>? token

fun isImmutable x =
  List.exists (fn x' => x' = x) ["true", "false", "nil", "self", "super"] 
val immutable = sat isImmutable name

val mutable =
  let fun can'tMutate (loc, x) =
        ERROR (srclocString loc ^ ": you cannot set or val-bind pseudovariable "
                                                                            ^ x)
  in  can'tMutate <$>! @@ immutable <|> OK <$>! name
  end

val formals  = "(" >-- many name --< ")"
val bformals = blockDups <$>! @@ formals

fun exp tokens = (
  (* must be allowed to fail since it is used in 'many exp' *)
      (LITERAL o NUM)    <$> int
  <|> (LITERAL o SYM)    <$> sym
  <|> SUPER              <$  literal "super"
  <|> VAR                <$> name
  <|> literal "#" *> (   (LITERAL o SYM)                <$> name
                    <|>  (LITERAL o SYM o Int.toString) <$> int
                    <|>  VALUE                          <$> sharp
                            (* last better not happen in initial basis *)
                    )
  <|> bracket "set"   "(set x e)"             (curry SET   <$> mutable <*> exp)
  <|> bracket "begin" "(begin e ...)"         (      BEGIN <$> many exp)
  <|> bracket "block" "(block (x ...) e ...)" (curry BLOCK <$> bformals <*> many
                                                                            exp)
  <|> bracket "locals" "expression" 
                  (errorAt
                         "found '(locals ...)' where an expression was expected"
                   <$>! srcloc)
  <|> curry BLOCK [] <$> "[" >-- many exp  --< "]"
  <|> messageSend    <$> "(" >-- @@ name <*> exp <*>! many exp --< ")"
  <|> (fn (loc, n) => errorAt ("sent message " ^ n ^ " to no object") loc) <$>! 
      "(" >-- @@ name --< ")"
  <|> "(" >-- literal ")" <!> "empty message send ()"
  ) 
  tokens
and messageSend (loc, msgname) receiver args =
      if arityOk msgname args then
          OK (SEND (loc, msgname, receiver, args))
      else
          arityErrorAt loc "message send" msgname args
(* parsing ((usm)) 703 *)
and sharp tokens = (
         mkSymbol  <$> name
    <|>  mkInteger <$> int
    <|>  mkArray   <$> ("(" >-- many sharp --< ")")
    <|>  literal "#" <!> "# within # is not legal" 
    <|>  literal "[" <!> "[ within # is not legal"
    <|>  literal "]" <!> "] within # is not legal"
    ) tokens
(* parsing ((usm)) 704 *)

type 'a located = srcloc * 'a

fun def tokens = (
     bracket "define" "(define f (args) body)"
                  (curry3 DEFINE <$> name <*> formals <*> exp)
  <|> bracket "class" "(class name super (instance vars) methods)"
                  (classDef      <$> name <*> name <*> @@ formals <*>! many
                                                                         method)
  <|> bracket "val"   "(val x e)"      (curry VAL <$> mutable <*> exp)
  <|> bracket "use"   "(use filename)" (      USE <$> name)
  <|> bracket "method" ""              (badDecl "method") 
  <|> bracket "class-method" ""        (badDecl "class-method")
  <|> literal ")" <!> "unexpected right parenthesis"
  <|> EXP <$> exp
  <?> "definition"
  ) tokens

and classDef name super ivars methods =
      (ivarDups name ivars) >>=+ (fn ivars =>
      CLASSD { name = name, super = super, ivars = ivars, methods = methods })

and method tokens =
  let datatype ('a, 'b) imp = PRIM of 'a | USER of 'b
      val user : string list located * string list located * exp list ->
                 (string, string list located * string list located * exp list)
                                                                      imp = USER
      fun imp kind =  PRIM <$> "primitive" >-- name
                  <|> curry3 USER <$> @@ formals <*> @@ locals <*> many exp
      and locals tokens =
            (bracket "locals" "(locals ivars)" (many name) <|> pure []) tokens

      fun method kind name impl =
        check (kname kind, name, impl) >>= (fn impl => OK (kind, name, impl))
      and kname IMETHOD = "method"
        | kname CMETHOD = "class-method"
      and check (_, _, PRIM p) = OK (PRIM_IMPL p)  (* no checking possible *)
        | check (kind, name, USER (formals as (loc, _), locals, body)) = 
            methodDups kind name formals >>= (fn formals => 
            localDups  kind name locals  >>= (fn locals => 
                if arityOk name formals then
                  OK (USER_IMPL (formals, locals, BEGIN body))
                else
                  arityErrorAt loc (kind ^ " definition") name formals))

      val name' = (fn n => ((*app print ["Parsing method ", n, "\n"];*) n)) <$>
                                                                            name
  in   bracket "method"       "(method f (args) body)" 
                                    (method IMETHOD <$> name' <*>! imp "method")
   <|> bracket "class-method" "(class-method f (args) body)"
                                    (method CMETHOD <$> name' <*>! imp
                                                                 "class method")
  end tokens

and badDecl what =
  errorAt ("unexpected `(" ^ what ^ "...'; " ^
           "did a class definition end prematurely?") <$>! srcloc
(* parsing ((usm)) 705a *)
val smalltalkSyntax = (smalltalkToken, def)


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVE BASICS                                            *)
(*                                                               *)
(*****************************************************************)

(* primitive basics 478b *)
type primitive = value * value list -> value
fun arityError n (receiver, args) =
  raise RuntimeError ("primitive method expected " ^ Int.toString n ^
                      " arguments; got " ^ Int.toString (length args))
fun unaryPrim  f = (fn (a, [])  => f  a     | ra => arityError 0 ra)
fun binaryPrim f = (fn (a, [b]) => f (a, b) | ra => arityError 1 ra)
fun primMethod name f = PRIM_METHOD (name, f)
(* type declarations for consistency checking *)
val _ = op unaryPrim  : (value         -> value) -> primitive
val _ = op binaryPrim : (value * value -> value) -> primitive
val _ = op primMethod : name -> primitive -> method
(* primitive basics 479a *)
fun userMethod name formals locals body = 
  let val bogusSuper = CLASS { name = "should never be used", super = NONE,
                               ivars = [], methods = [], id = 0 }
  in  USER_METHOD { name = name, formals = formals, locals = locals,
                    body = internalExp body, superclass = bogusSuper }
  end
and internalExp s = 
  let val name = "internal expression \"" ^ s ^ "\""
      val parser = exp <?> "expression"
      val input = reader (smalltalkToken, parser) noPrompts (name, streamOfList
                                                                            [s])
      exception BadUserMethodInInterpreter of string (* can't be caught *)
  in  case streamGet input
        of SOME (e, _) => e
         | NONE => raise BadUserMethodInInterpreter s
  end
(* type declarations for consistency checking *)
val _ = op internalExp : string -> exp


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVE METHODS FOR [[OBJECT]] AND [[UNDEFINEDOBJECT]]    *)
(*                                                               *)
(*****************************************************************)

(* primitive methods for [[Object]] and [[UndefinedObject]] 479b *)
fun eqRep ((cx, x), (cy, y)) = 
  classId cx = classId cy andalso
  case (x, y)
    of (ARRAY x,    ARRAY    y) => x = y
     | (NUM   x,    NUM      y) => x = y
     | (SYM   x,    SYM      y) => x = y
     | (USER  x,    USER     y) => x = y
     | (CLOSURE  x, CLOSURE  y) => false
     | (CLASSREP x, CLASSREP y) => classId x = classId y
     | _ => false
(* type declarations for consistency checking *)
val _ = op eqRep : value * value -> bool
(* primitive methods for [[Object]] and [[UndefinedObject]] 480b *)
fun defaultPrint (self as (c, _)) = ( app print ["<", className c, ">"]; self )
(* primitive methods for [[Object]] and [[UndefinedObject]] 480d *)
fun memberOf ((c, _), (_, CLASSREP c')) = mkBoolean (classId c = classId c')
  | memberOf _ = raise RuntimeError "argument of isMemberOf: must be a class"

fun kindOf ((c, _), (_, CLASSREP (CLASS {id=u', ...}))) =
      let fun subclassOfClassU' (CLASS {super, id=u, ... }) =
            u = u' orelse (case super of NONE => false | SOME c =>
                                                            subclassOfClassU' c)
      in  mkBoolean (subclassOfClassU' c)
      end
  | kindOf _ = raise RuntimeError "argument of isKindOf: must be a class"
(* primitive methods for [[Object]] and [[UndefinedObject]] 480e *)
fun error (_, (_, SYM s)) = raise RuntimeError s
  | error (_, (c, _    )) =
      raise RuntimeError ("error: got class " ^ className c ^
                                                            "; expected Symbol")


(*****************************************************************)
(*                                                               *)
(*   BUILT-IN CLASSES [[OBJECT]] AND [[UNDEFINEDOBJECT]]         *)
(*                                                               *)
(*****************************************************************)

(* built-in classes [[Object]] and [[UndefinedObject]] 485a *)
val objectClass = 
  CLASS { name = "Object", super = NONE, ivars = ["self"], id = 1
        , methods = methods
            [ primMethod "print"   (unaryPrim defaultPrint)
            , userMethod "println" [] []
                                     "(begin (print self) (print newline) self)"
            , primMethod "isNil"   (unaryPrim (fn _ => mkBoolean false))
            , primMethod "notNil"  (unaryPrim (fn _ => mkBoolean true))
            , primMethod "error:"  (binaryPrim error)
            , primMethod "="       (binaryPrim (mkBoolean o eqRep))
            , userMethod "!=" ["x"] [] "(not (= self x))"
            , primMethod "isKindOf:"    (binaryPrim kindOf)
            , primMethod "isMemberOf:"  (binaryPrim memberOf)
            , primMethod "subclassResponsibility"
               (unaryPrim
                  (fn _ => raise RuntimeError

           "subclass failed to implement a method that was its responsibility"))
            ]
        }
(* built-in classes [[Object]] and [[UndefinedObject]] 485b *)
val nilClass = 
  mkClass "UndefinedObject" objectClass []
    [ primMethod "isNil"  (unaryPrim (fn _ => mkBoolean true))
    , primMethod "notNil" (unaryPrim (fn _ => mkBoolean false))
    , primMethod "print"  (unaryPrim (fn x => (print "nil"; x)))
    ]
(* built-in classes [[Object]] and [[UndefinedObject]] 485c *)
val nilValue = 
  let val nilCell  = ref (nilClass, USER []) : value ref
      val nilValue = (nilClass, USER (bind ("self", nilCell, emptyEnv)))
      val _        = nilCell := nilValue
  in  nilValue
  end


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVE METHODS FOR REMAINING CLASSES                     *)
(*                                                               *)
(*****************************************************************)

(* primitive methods for remaining classes 480f *)
fun printInt (self as (_, NUM n)) =
      ( print (String.map (fn #"~" => #"-" | c => c) (Int.toString n))
      ; self
      )
  | printInt _ =
      raise RuntimeError ("cannot print when object inherits from Int")
(* primitive methods for remaining classes 481a *)
fun binaryInt mk $ ((_, NUM n), (_, NUM m)) = mk ($ (n, m))
  | binaryInt _ _  ((_, NUM n), (c, _)) =
      raise RuntimeError ("numeric primitive expected numeric argument, got <"
                          ^ className c ^ ">")
  | binaryInt _ _  ((c, _), _) =
      raise RuntimeError ("numeric primitive method defined on <" ^ className c
                                                                          ^ ">")
fun arithop    $ = binaryPrim (binaryInt mkInteger $)
fun intcompare $ = binaryPrim (binaryInt mkBoolean $)
(* primitive methods for remaining classes 481b *)
fun newInteger ((_, CLASSREP c), (_, NUM n)) = (c, NUM n)
  | newInteger _ = raise RuntimeError (
                                   "made new integer with non-int or non-class")
(* primitive methods for remaining classes 481d *)
fun printSymbol (self as (_, SYM s)) = (print s; self)
  | printSymbol _ = raise RuntimeError
                                 "cannot print when object inherits from Symbol"
(* primitive methods for remaining classes 481e *)
fun newSymbol ((_, CLASSREP c), (_, SYM s)) = (c, SYM s)
  | newSymbol _ = raise RuntimeError (
                                 "made new symbol with non-symbol or non-class")
(* primitive methods for remaining classes 482b *)
fun newArray ((_, CLASSREP c), (_, NUM n)) = (c, ARRAY (Array.array (n, nilValue
                                                                             )))
  | newArray _ = raise RuntimeError
                                "Array new sent to non-class or got non-integer"
(* primitive methods for remaining classes 482c *)
fun arrayPrimitive f ((_, ARRAY a), l) = f (a, l)
  | arrayPrimitive f _ = raise RuntimeError "Array primitive used on non-array"

fun arraySize (a, []) = mkInteger (Array.length a)
  | arraySize ra      = arityError 0 ra
(* primitive methods for remaining classes 482d *)
fun arrayAt (a, [(_, NUM n)]) = Array.sub (a, n - 1)  (* convert to 0-indexed *)
  | arrayAt (_, [_])  = raise RuntimeError "Non-integer used as array subscript"
  | arrayAt ra        = arityError 1 ra

fun arrayAtPut (a, [(_, NUM n), x]) = (Array.update (a, n-1, x); x)
  | arrayAtPut (_, [_, _]) = raise RuntimeError
                                           "Non-integer used as array subscript"
  | arrayAtPut ra          = arityError 2 ra
(* primitive methods for remaining classes 483a *)
fun classPrimitive f = 
  unaryPrim (fn (meta, CLASSREP c) => f (meta, c)
              | _ => raise RuntimeError "class primitive sent to non-class")
(* type declarations for consistency checking *)
val _ = op binaryInt  : ('a -> value) -> (int * int -> 'a)   -> value * value ->
                                                                           value
val _ = op arithop    :                  (int * int -> int)  -> primitive
val _ = op intcompare :                  (int * int -> bool) -> primitive
(* type declarations for consistency checking *)
val _ = op arrayPrimitive : (value array * value list -> value) -> primitive
(* type declarations for consistency checking *)
val _ = op classPrimitive : (class * class -> value) -> primitive
(* primitive methods for remaining classes 483b *)
local
  fun mkIvars (CLASS { ivars, super, ... }) =
    let val supervars = case super of NONE => emptyEnv | SOME c => mkIvars c
    in  foldl (fn (n, rho) => bind (n, ref nilValue, rho)) supervars ivars
    end
in
  fun newUserObject (_, c) =
        let val ivars = mkIvars c
            val self = (c, USER ivars)
        in  (find ("self", ivars) := self; self)
        end
(* type declarations for consistency checking *)
val _ = op mkIvars       : class -> value ref env
val _ = op newUserObject : class * class -> value
end
(* primitive methods for remaining classes 484 *)
(* definition of [[separate]] 218d *)
fun separate (zero, sep) =  (* print list with separator *)
  let fun s []     = zero
        | s [x]    = x
        | s (h::t) = h ^ sep ^ s t
  in  s
end
val spaceSep = separate ("", " ")  (* print separated by spaces *)
local
  fun showProtocol doSuper kind c =
    let fun member x l = List.exists (fn x' : string => x' = x) l
        fun insert (x, []) = [x]
          | insert (x, (h::t)) =
              case compare x h
                of LESS    => x :: h :: t
                 | EQUAL   => x :: t (* replace *)
                 | GREATER => h :: insert (x, t)
        and compare (name, _) (name', _) = String.compare (name, name')
        fun methods (CLASS { super, methods = ms, name, ... }) =
              if not doSuper orelse (kind = "class-method" andalso name =
                                                                   "Class") then
                foldl insert [] ms
              else
                foldl insert (case super of NONE => [] | SOME c => methods c) ms
        fun show (name, PRIM_METHOD _) =
              app print ["(", kind, " ", name, " primitive ...)\n"]
          | show (name, USER_METHOD { formals, ... }) =
              app print ["(", kind, " ", name,
                         " (", spaceSep formals, ") ...)\n"]
    in  app show (methods c)
    end
in
  fun protocols all (meta, c) =
    ( showProtocol all "class-method" meta
    ; showProtocol all "method" c
    ; (meta, CLASSREP c)
    )
end
(* primitive methods for remaining classes 519a *)
fun withOverflow binop ((_, NUM n), [(_, NUM m), ovflw]) = 
      (mkBlock ([], [VALUE (mkInteger (binop (n, m)))], emptyEnv, objectClass)
       handle Overflow => ovflw)
  | withOverflow _ (_, [_, _]) =
      raise RuntimeError "numeric primitive with overflow expects numbers"
  | withOverflow _ _ =
      raise RuntimeError
                     "numeric primitive with overflow expects receiver + 2 args"


(*****************************************************************)
(*                                                               *)
(*   REMAINING BUILT-IN CLASSES                                  *)
(*                                                               *)
(*****************************************************************)

(* remaining built-in classes 485d *)
val classClass =
  mkClass "Class" objectClass []
    [ primMethod "new"           (classPrimitive newUserObject) 
    , primMethod "protocol"      (classPrimitive (protocols true))
    , primMethod "localProtocol" (classPrimitive (protocols false))
    ]


(*****************************************************************)
(*                                                               *)
(*   IMPLEMENTATION OF [[USE]], WITH BOOLEAN [[ECHO]]            *)
(*                                                               *)
(*****************************************************************)

(* implementation of [[use]], with Boolean [[echo]] 707b *)
fun use readEvalPrint filename rho =
      let val fd = TextIO.openIn filename
          val defs = reader smalltalkSyntax noPrompts (filename, streamOfLines
                                                                             fd)
          fun errln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      in  readEvalPrint (defs, true, errln) rho
          before TextIO.closeIn fd
      end 


(*****************************************************************)
(*                                                               *)
(*   EVALUATION                                                  *)
(*                                                               *)
(*****************************************************************)

(* evaluation ((usm)) 486a *)
(* tracing ((usm)) 705b *)
local
  (* private state and functions for printing indented traces ((usm)) 705c *)
  fun traceMe xi =
    let val count = find("&trace", xi)
    in  case !count
          of (c, NUM n) =>
              if n = 0 then false
              else ( count := (c, NUM (n - 1))
                   ; if n = 1 then (print "<trace ends>\n"; false) else true
                   )
           | _ => false
    end handle NotFound _ => false
  (* type declarations for consistency checking *)
  val _ = op name : string parser
  val _ = op int  : int    parser
  (* type declarations for consistency checking *)
  val _ = op traceMe : value ref env -> bool
  (* private state and functions for printing indented traces ((usm)) 705d *)
  val tindent = ref 0
  fun indent 0 = ()
    | indent n = (print "  "; indent (n-1))
  (* private state and functions for printing indented traces ((usm)) 706a *)
  datatype indentation = INDENT_AFTER | OUTDENT_BEFORE

  fun tracePrint direction xi f =
      if traceMe xi then
        let val msg = f () (* could change tindent *)
        in  ( if direction = OUTDENT_BEFORE then tindent := !tindent - 1 else ()
            ; indent (!tindent)
            ; app print msg
            ; print "\n"
            ; if direction = INDENT_AFTER   then tindent := !tindent + 1 else ()
            )
        end
      else
          ()    
  (* private state and functions for mainting a stack of source-code locations (
                                                                  (usm)) 706b *)
  val locationStack = ref [] : (string * srcloc) list ref
  fun push srcloc = locationStack := srcloc :: !locationStack
  fun pop () = case !locationStack
                 of []     => raise InternalError "tracing stack underflows"
                  | h :: t => locationStack := t
in
  (* exposed tracing functions ((usm)) 706c *)
  fun resetTrace ()       = (locationStack := []; tindent := 0)
  fun traceIndent what xi = (push what; tracePrint INDENT_AFTER   xi)
  fun outdentTrace     xi = (pop ();    tracePrint OUTDENT_BEFORE xi)
  fun showStackTrace () =
    let fun show (msg, (file, n)) =
          app print ["  Sent '", msg, "' in ", file, ", line ", Int.toString n,
                                                                           "\n"]
    in  case !locationStack
          of [] => ()
           | l  => ( print "Method-stack traceback:\n"; app show (!locationStack
                                                                             ) )
    end
  (* type declarations for consistency checking *)
  val _ = op resetTrace     : unit -> unit
  val _ = op traceIndent    : string * srcloc -> value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op outdentTrace   :                    value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op showStackTrace : unit -> unit
end
(* tracing ((usm)) 707a *)
fun valueString (c, NUM n) = 
      String.map (fn #"~" => #"-" | c => c) (Int.toString n) ^
      valueString(c, USER [])
  | valueString (_, SYM v) = v
  | valueString (c, _) = "<" ^ className c ^ ">"
fun eval (e, rho, superclass, xi) =
  let (* local helper functions of [[eval]] 486b *)
      fun findMethod (name, class) =
        let fun fm (CLASS { methods, super, ...}) =
              find (name, methods)
              handle NotFound m =>
                case super
                  of SOME c => fm c
                   | NONE   => raise RuntimeError
                                 (className class ^
                                            " does not understand message " ^ m)
      (* type declarations for consistency checking *)
      val _ = op findMethod : name * class -> method
      val _ = op fm         : class        -> method
        in  fm class
        end
      (* local helper functions of [[eval]] 487a *)
      fun evalMethod (PRIM_METHOD (name, f), receiver, actuals) = f (receiver,
                                                                        actuals)
        | evalMethod (USER_METHOD { name, superclass, formals, locals, body },
                      receiver, actuals) =
            let val rho'  = instanceVars receiver
                val rho_x = bindList (formals, map ref actuals, rho')
                val rho_y = bindList (locals, map (fn _ => ref nilValue) locals,
                                                                          rho_x)
            in  eval (body, rho_y, superclass, xi)
            end
              handle BindListLength => 
                  raise RuntimeError
                      ("Wrong number of arguments to method " ^ name ^
                                                                "; expected (" ^
                       spaceSep (name :: "self" :: formals) ^ ")")
      and instanceVars (_, USER rep) = rep
        | instanceVars self = bind ("self", ref self, emptyEnv)
      (* type declarations for consistency checking *)
      val _ = op evalMethod   : method * value * value list -> value
      val _ = op instanceVars : value -> value ref env
      (* local helper functions of [[eval]] 487b *)
      fun applyClosure ((formals, body, rho, superclass), actuals) =
        eval (BEGIN body, bindList (formals, map ref actuals, rho), superclass,
                                                                             xi)
        handle BindListLength => 
            raise RuntimeError ("Wrong number of arguments to block; expected "
                                                                               ^
                                "(value <block>" ^ spaceSep formals ^ ")")
      (* type declarations for consistency checking *)
      val _ = op applyClosure : (name list * exp list * value ref env * class) *
                                                             value list -> value
      (* function [[ev]], the evaluator proper ((usm)) 488a *)
      fun ev (VALUE v) = v
      (* function [[ev]], the evaluator proper ((usm)) 488b *)
        | ev (LITERAL c) = 
            (case c of NUM n => mkInteger n
                     | SYM n => mkSymbol n
                     | _ => raise InternalError "unexpected literal")
      (* function [[ev]], the evaluator proper ((usm)) 488c *)
        | ev (VAR v) = !(find (v, rho) handle NotFound _ => find (v, xi))
        | ev (SET (n, e)) =
            let val v = ev e
                val cell = find (n, rho) handle NotFound _ => find (n, xi)
            in  cell := v; v
            end 
      (* function [[ev]], the evaluator proper ((usm)) 488d *)
        | ev (SUPER) = ev (VAR "self")
      (* function [[ev]], the evaluator proper ((usm)) 489a *)
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, nilValue)
            end
      (* function [[ev]], the evaluator proper ((usm)) 489b *)
        | ev (BLOCK (formals, body)) = mkBlock (formals, body, rho, superclass)
      (* function [[ev]], the evaluator proper ((usm)) 490 *)
        | ev (SEND (srcloc, message, receiver, args))  =
            let val obj as (class, rep) = ev receiver
                val args = map ev args
                val dispatchingClass = case receiver of SUPER => superclass | _
                                                                        => class
                (* definitions of message-tracing procedures 491 *)
                fun traceSend (file, line) =
                  traceIndent (message, (file, line)) xi (fn () =>
                     [file, ", line ", Int.toString line, ": ",
                      "Sending message (", spaceSep (message :: map valueString
                                                                     args), ")",
                      " to object of class ", className dispatchingClass])
                fun traceAnswer (file, line) answer =
                  ( outdentTrace xi (fn () =>
                       [file, ", line ", Int.toString line, ": ",
                        "(", spaceSep (message :: map valueString (obj :: args))
                                                                          , ")",
                        " = ", valueString answer])
                  ; answer
                  )
                fun performSend () =
                  case (message, rep)
                    of ("value", CLOSURE clo) => applyClosure (clo, args)
                     | _ => evalMethod (findMethod (message, dispatchingClass),
                                                                      obj, args)

            in  ( traceSend srcloc
                ; traceAnswer srcloc (performSend ())
                )
            end
      (* type declarations for consistency checking *)
      val _ = op ev : exp -> value
(* type declarations for consistency checking *)
val _ = op eval: exp * value ref env * class * value ref env -> value
val _ = op ev  : exp -> value
  in  ev e
  end
(* evaluation ((usm)) 492a *)
(* definition of function [[primitiveMethod]] 492c *)
val primitiveMethods = methods ((* primitive methods [[::]] 480a *)
                                primMethod "eqObject" (binaryPrim (mkBoolean o
                                                                      eqRep)) ::
                                (* primitive methods [[::]] 480c *)
                                primMethod "print" (unaryPrim defaultPrint) ::
                                (* primitive methods [[::]] 481c *)
                                primMethod "printSmallInteger" (unaryPrim
                                                                    printInt) ::
                                primMethod "newSmallInteger:"  (binaryPrim
                                                                  newInteger) ::
                                primMethod "+"   (arithop op +  )  ::
                                primMethod "-"   (arithop op -  )  ::
                                primMethod "*"   (arithop op *  )  ::
                                primMethod "div" (arithop op div)  ::
                                primMethod "<"   (intcompare op <) ::
                                primMethod ">"   (intcompare op >) ::
                                (* primitive methods [[::]] 481f *)
                                primMethod "printSymbol" (unaryPrim  printSymbol
                                                                            ) ::
                                primMethod "newSymbol"   (binaryPrim newSymbol
                                                                            ) ::
                                (* primitive methods [[::]] 482e *)
                                primMethod "arrayNew:"    (binaryPrim
                                                                  newArray)   ::
                                primMethod "arraySize"    (arrayPrimitive
                                                                  arraySize)  ::
                                primMethod "arrayAt:"     (arrayPrimitive
                                                                  arrayAt)    ::
                                primMethod "arrayAt:Put:" (arrayPrimitive
                                                                  arrayAtPut) ::
                                (* primitive methods [[::]] 482f *)
                                primMethod "value" (fn _ => raise InternalError
                                              "hit primitive method 'value'") ::
                                (* primitive methods [[::]] 519b *)
                                primMethod "add:withOverflow:" (withOverflow op
                                                                          + ) ::
                                primMethod "sub:withOverflow:" (withOverflow op
                                                                          - ) ::
                                primMethod "mul:withOverflow:" (withOverflow op
                                                                     * ) :: nil)
fun primitiveMethod name =
  find (name, primitiveMethods)
  handle NotFound n => raise RuntimeError ("There is no primitive method named "
                                                                            ^ n)
fun newClassObject {name, super, ivars, methods = ms} xi =
  let val (superMeta, super) = findClass (super, xi)
        handle NotFound s => raise RuntimeError ("Superclass " ^ s ^
                                                                   " not found")
      fun method (kind, name, PRIM_IMPL prim) =
            renameMethod (name, primitiveMethod prim)
        | method (kind, name, USER_IMPL (formals, ls, body)) =
            USER_METHOD { name = name, formals = formals, body = body, locals =
                                                                              ls
                        , superclass = case kind of IMETHOD => super
                                                  | CMETHOD => superMeta
                        }
      fun addMethodDefn (m as (CMETHOD, _, _), (c's, i's)) = (method m :: c's,
                                                                            i's)
        | addMethodDefn (m as (IMETHOD, _, _), (c's, i's)) = (c's, method m ::
                                                                            i's)
      val (cmethods, imethods) = foldr addMethodDefn ([], []) ms
      val metaclassName = "class " ^ name
      val class     = mkClass name          super      ivars imethods
      val metaclass = mkClass metaclassName superMeta  []    cmethods
(* type declarations for consistency checking *)
val _ = op primitiveMethod : name -> method
  in  (metaclass, CLASSREP class)
  end
(* evaluation ((usm)) 492b *)
and findClass (supername, xi) =
  case !(find (supername, xi))
    of (meta, CLASSREP c) => (meta, c)
     | v => raise RuntimeError ("object " ^ supername ^ " = " ^ valueString v ^
                                " is not a class")
(* evaluation ((usm)) 493a *)
fun evaldef (d, echo, xi)  =
  case d
    of VAL (name, e) => doVal echo (name, eval (e, emptyEnv, objectClass, xi),
                                                                             xi)
     | EXP e                     => evaldef (VAL ("it", e),
                                                                       echo, xi)
     | DEFINE (name, args, body) => evaldef (VAL (name, BLOCK (args, [body])),
                                                                       echo, xi)
     | CLASSD (d as {name, ...}) => doVal echo (name, newClassObject d xi, xi)
     | USE filename              => use readEvalPrint filename xi 
(* evaluation ((usm)) 493b *)
and doVal echo (name, value, xi)  =
      ( (find (name, xi) := value; xi)
        handle NotFound _ => bind (name, ref value, xi)
      )
      before printValue echo xi value
(* evaluation ((usm)) 493c *)
and printValue echo xi v = 
  if echo then
    ( eval (SEND (nullsrc, "print", VALUE v, []), emptyEnv, objectClass, xi)
    ; print "\n"
    )
  else
    ()
(* evaluation ((usm)) 494a *)
and readEvalPrint (defs : def stream, echo, errmsg) xi =
  let fun processDef (def, xi) =
        let fun continue msg = (errmsg msg; showStackTrace (); resetTrace (); xi
                                                                               )
            val _ = (closeLiteralsCycle xi; closeBlocksCycle xi)
                    handle NotFound _ => ()
            in  evaldef (def, echo, xi)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* more read-eval-print handlers ((usm)) 494b *)
                | Subscript       => continue ("array subscript out of bounds")
                | Size            => continue ("bad array size")
                (* more read-eval-print handlers 222c *)
                (* more read-eval-print handlers 223a *)
                | Div               => continue "Division by zero"
                | Overflow          => continue "Arithmetic overflow"
                | RuntimeError msg  => continue ("run-time error: " ^ msg)
                | NotFound n        => continue ("variable " ^ n ^ " not found")
            end
  in  streamFold processDef xi (defs : def stream)
  end
(* type declarations for consistency checking *)
val _ = op findClass : name * value ref env -> class * class
(* type declarations for consistency checking *)
val _ = op evaldef : def * bool * value ref env -> value ref env


(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION                                              *)
(*                                                               *)
(*****************************************************************)

(* initialization ((usm)) 494c *)
val initialXi = emptyEnv

fun mkMeta c = mkClass ("class " ^ className c) classClass [] []
fun addClass (c, xi) = bind (className c, ref (mkMeta c, CLASSREP c), xi)
val initialXi = foldl addClass initialXi [ objectClass, nilClass, classClass ]
(* initialization ((usm)) 495a *)
val echoBasis = false
val initialXi =
  let val defs = reader smalltalkSyntax noPrompts
                 ("initial basis", streamOfList (* ML representation of initial
                                                basis (generated by a script) *)

                                                 [ "(class Boolean Object ()"
                                                 ,
"    (method ifTrue:ifFalse: (trueBlock falseBlock) (subclassResponsibility self))"
                                                 , "  "
                                                 ,
                           "    (method ifFalse:ifTrue: (falseBlock trueBlock) "
                                                 ,
                          "        (ifTrue:ifFalse: self trueBlock falseBlock))"
                                                 ,
        "    (method ifTrue:  (trueBlock)  (ifTrue:ifFalse: self trueBlock []))"
                                                 ,
       "    (method ifFalse: (falseBlock) (ifTrue:ifFalse: self [] falseBlock))"
                                                 , "    "
                                                 ,
   "    (method not ()          (ifTrue:ifFalse: self [false]          [true]))"
                                                 ,
"    (method eqv: (aBoolean) (ifTrue:ifFalse: self [aBoolean]       [(not aBoolean)]))"
                                                 ,
"    (method xor: (aBoolean) (ifTrue:ifFalse: self [(not aBoolean)] [aBoolean]))"
                                                 , ""
                                                 ,
            "    (method & (aBoolean) (ifTrue:ifFalse: self [aBoolean] [self]))"
                                                 ,
            "    (method | (aBoolean) (ifTrue:ifFalse: self [self] [aBoolean]))"
                                                 , "  "
                                                 ,
"    (method and: (alternativeBlock) (ifTrue:ifFalse: self alternativeBlock [self]))"
                                                 ,
"    (method or:  (alternativeBlock) (ifTrue:ifFalse: self [self] alternativeBlock))"
                                                 , ""
                                                 ,
"    (method if (trueBlock falseBlock) (ifTrue:ifFalse: self trueBlock falseBlock))"
                                                 , ")"
                                                 , "(class True Boolean ()"
                                                 ,
           "  (method ifTrue:ifFalse: (trueBlock falseBlock) (value trueBlock))"
                                                 , ")"
                                                 , "(class False Boolean ()"
                                                 ,
          "  (method ifTrue:ifFalse: (trueBlock falseBlock) (value falseBlock))"
                                                 , ")"
                                                 , "(class Block Object "
                                                 ,
                                              "    () ; internal representation"
                                                 ,
                                            "    (method value primitive value)"
                                                 ,
                                                 "    (method whileTrue: (body)"
                                                 ,
                                         "        (ifTrue:ifFalse: (value self)"
                                                 , "            [(value body)"
                                                 ,
                                          "             (whileTrue: self body)]"
                                                 , "            [nil]))"
                                                 ,
                              "    (method while (body) (whileTrue: self body))"
                                                 ,
                                               "    (method whileFalse: (body) "
                                                 ,
                                        "         (ifTrue:ifFalse: (value self)"
                                                 ,
                                                "             [nil]            "
                                                 , "             [(value body) "
                                                 ,
                                      "              (whileFalse: self body)]))"
                                                 , ")"
                                                 , "(class Symbol Object"
                                                 ,
                                              "    () ; internal representation"
                                                 ,
             "    (class-method new () (error: self #can't-send-new-to-Symbol))"
                                                 ,
                                 "    (class-method new:   primitive newSymbol)"
                                                 ,
                               "    (method       print  primitive printSymbol)"
                                                 , ")"
                                                 , "(class Magnitude Object "
                                                 , "    () ; abstract class"
                                                 ,
"    (method =  (x) (subclassResponsibility self)) ; may not inherit from Object"
                                                 ,
                             "    (method <  (x) (subclassResponsibility self))"
                                                 ,
                                                "    (method >  (y) (< y self))"
                                                 ,
                                          "    (method <= (x) (not (> self x)))"
                                                 ,
                                          "    (method >= (x) (not (< self x)))"
                                                 ,
   "    (method min: (aMagnitude) (if (< self aMagnitude) [self] [aMagnitude]))"
                                                 ,
   "    (method max: (aMagnitude) (if (> self aMagnitude) [self] [aMagnitude]))"
                                                 , ")"
                                                 , "(class Number Magnitude"
                                                 , "    ()  ; abstract class"
                                                 ,
                                             "    ;;;;;;; basic Number protocol"
                                                 ,
                  "    (method +   (aNumber)     (subclassResponsibility self))"
                                                 ,
                  "    (method *   (aNumber)     (subclassResponsibility self))"
                                                 ,
                  "    (method negated    ()     (subclassResponsibility self))"
                                                 ,
                  "    (method reciprocal ()     (subclassResponsibility self))"
                                                 , "    "
                                                 ,
                  "    (method asInteger  ()     (subclassResponsibility self))"
                                                 ,
                  "    (method asFraction ()     (subclassResponsibility self))"
                                                 ,
                  "    (method asFloat    ()     (subclassResponsibility self))"
                                                 ,
                  "    (method coerce: (aNumber) (subclassResponsibility self))"
                                                 ,
                                    "    (method -   (y) (+ self (negated  y)))"
                                                 ,
            "    (method abs ()  (if (negative self) [(negated  self)] [self]))"
                                                 ,
                                  "    (method /   (y) (* self (reciprocal y)))"
                                                 ,
                   "    (method negative         () (<  self (coerce: self 0)))"
                                                 ,
                   "    (method positive         () (>= self (coerce: self 0)))"
                                                 ,
                   "    (method strictlyPositive () (>  self (coerce: self 0)))"
                                                 ,
                                         "    (method squared () (* self self))"
                                                 ,
                                      "    (method raisedToInteger: (anInteger)"
                                                 , "        (if (= anInteger 0)"
                                                 ,
                                                "            [(coerce: self 1)]"
                                                 ,
                                       "            [(if (= anInteger 1) [self]"
                                                 ,
      "                [(* (squared (raisedToInteger: self (div: anInteger 2)))"
                                                 ,
          "                    (raisedToInteger: self (mod: anInteger 2)))])]))"
                                                 ,
               "    (method sqrt () (sqrtWithin: self (coerce: self (/ 1 10))))"
                                                 ,
                  "    (method sqrtWithin: (epsilon) (locals two x_{i-1} x_{i})"
                                                 ,
                         "        ; find square root of receiver within epsilon"
                                                 ,
                                        "        (set two     (coerce: self 2))"
                                                 ,
                                        "        (set x_{i-1} (coerce: self 1))"
                                                 ,
                    "        (set x_{i}   (/ (+ x_{i-1} (/ self x_{i-1})) two))"
                                                 ,
                          "        (while [(> (abs (- x_{i-1} x_{i})) epsilon)]"
                                                 ,
                                           "               [(set x_{i-1} x_{i})"
                                                 ,
            "                (set x_{i} (/ (+ x_{i-1} (/ self x_{i-1})) two))])"
                                                 , "        x_{i})"
                                                 , ")"
                                                 , "(class Integer Number"
                                                 , "    () ; abstract class"
                                                 ,
                           "    (method div: (n) (subclassResponsibility self))"
                                                 ,
                            "    (method mod: (n) (- self (* n (div: self n))))"
                                                 ,
"    (method gcd: (n) (if (= n (coerce: self 0)) [self] [(gcd: n (mod: self n))]))"
                                                 ,
                         "    (method lcm: (n) (* self (div: n (gcd: self n))))"
                                                 ,
                        "    (method asFraction () (num:den:  Fraction self 1))"
                                                 ,
                        "    (method asFloat    () (mant:exp: Float    self 0))"
                                                 ,
                                               "    (method asInteger  () self)"
                                                 ,
                            "    (method coerce: (aNumber) (asInteger aNumber))"
                                                 ,
                        "    (method reciprocal () (num:den: Fraction 1 self)) "
                                                 ,
                        "    (method / (aNumber) (/ (asFraction self) aNumber))"
                                                 ,
                              "    (method timesRepeat: (aBlock) (locals count)"
                                                 ,
      "        (ifTrue: (negative self) [(error: self #negative-repeat-count)])"
                                                 , "        (set count self)"
                                                 ,
                                                 "        (while [(!= count 0)]"
                                                 ,
                                                  "             [(value aBlock)"
                                                 ,
                                      "              (set count (- count 1))]))"
                                                 , ")"
                                                 , "(class SmallInteger Integer"
                                                 ,
                                             "    () ; primitive representation"
                                                 ,
                            "    (class-method new: primitive newSmallInteger:)"
                                                 ,
                                     "    (class-method new   () (new: self 0))"
                                                 ,
                                        "    (method negated     () (- 0 self))"
                                                 ,
                                "    (method print primitive printSmallInteger)"
                                                 ,
                                                "    (method +     primitive +)"
                                                 ,
                                                "    (method -     primitive -)"
                                                 ,
                                                "    (method *     primitive *)"
                                                 ,
                                              "    (method div:  primitive div)"
                                                 ,
                                         "    (method =     primitive eqObject)"
                                                 ,
                                                "    (method <     primitive <)"
                                                 ,
                                                "    (method >     primitive >)"
                                                 , ")"
                                                 , "(class Fraction Number"
                                                 , "    (num den)"
                                                 ,
               "    (class-method num:den: (a b) (initNum:den: (new self) a b))"
                                                 ,
                                      "    (method initNum:den: (a b) ; private"
                                                 ,
                                                "        (setNum:den: self a b)"
                                                 , "        (signReduce self)"
                                                 , "        (divReduce self))"
                                                 ,
         "    (method setNum:den: (a b) (set num a) (set den b) self) ; private"
                                                 ,
                                           "    (method signReduce () ; private"
                                                 ,
                                               "        (ifTrue: (negative den)"
                                                 ,
                "            [(set num (negated num)) (set den (negated den))])"
                                                 , "        self)"
                                                 , ""
                                                 ,
                              "    (method divReduce () (locals temp) ; private"
                                                 , "        (if (= num 0)"
                                                 , "            [(set den 1)]"
                                                 ,
                                  "            [(set temp (gcd: (abs num) den))"
                                                 ,
                                       "             (set num  (div: num temp))"
                                                 ,
                                     "             (set den  (div: den temp))])"
                                                 , "        self)"
                                                 , "    (method num () num)"
                                                 , "    (method den () den)"
                                                 , "    (method = (f)"
                                                 ,
                             "        (and: (= num (num f)) [(= den (den f))]))"
                                                 , "    (method < (f)"
                                                 ,
                                  "        (< (* num (den f)) (* (num f) den)))"
                                                 ,
        "    (method negated () (setNum:den: (new Fraction) (negated num) den))"
                                                 , "    (method * (f)"
                                                 , "        (divReduce"
                                                 ,
                                       "            (setNum:den: (new Fraction)"
                                                 ,
                                   "                            (* num (num f))"
                                                 ,
                                "                            (* den (den f)))))"
                                                 ,
                                               "    (method + (f) (locals temp)"
                                                 ,
                                         "        (set temp (lcm: den (den f)))"
                                                 , "        (divReduce"
                                                 ,
                                       "            (setNum:den: (new Fraction)"
                                                 ,
"                         (+ (* num (div: temp den)) (* (num f) (div: temp (den f))))"
                                                 ,
                                              "                         temp)))"
                                                 , "    (method reciprocal ()"
                                                 ,
                     "       (signReduce (setNum:den: (new Fraction) den num)))"
                                                 ,
                 "    (method print () (print num) (print #/) (print den) self)"
                                                 ,
                                     "    (method asInteger  () (div: num den))"
                                                 ,
                    "    (method asFloat    () (/ (asFloat num) (asFloat den)))"
                                                 ,
                                               "    (method asFraction () self)"
                                                 ,
                           "    (method coerce: (aNumber) (asFraction aNumber))"
                                                 ,
                               "    (method negative         () (negative num))"
                                                 ,
                               "    (method positive         () (positive num))"
                                                 ,
                       "    (method strictlyPositive () (strictlyPositive num))"
                                                 , ")"
                                                 , "(class Float Number"
                                                 , "    (mant exp)"
                                                 ,
             "    (class-method mant:exp: (m e) (initMant:exp: (new self) m e))"
                                                 ,
                                     "    (method initMant:exp: (m e) ; private"
                                                 ,
                            "        (set mant m) (set exp e) (normalize self))"
                                                 ,
                                         "    (method normalize ()    ; private"
                                                 ,
                                         "        (while [(> (abs mant) 32767)]"
                                                 ,
                                     "               [(set mant (div: mant 10))"
                                                 ,
                                         "                (set exp (+ exp 1))])"
                                                 , "        self)"
                                                 ,
                                          "    (method mant () mant)  ; private"
                                                 ,
                                          "    (method exp  () exp)   ; private"
                                                 ,
                                      "    (method < (x) (negative (- self x)))"
                                                 ,
                                      "    (method = (x) (isZero   (- self x)))"
                                                 ,
                                             "    (method isZero () (= mant 0))"
                                                 ,
                  "    (method negated () (mant:exp: Float (negated mant) exp))"
                                                 , "    (method + (prime) "
                                                 ,
                                              "        (if (>= exp (exp prime))"
                                                 ,
"            [(mant:exp: Float (+ (* mant (raisedToInteger: 10 (- exp (exp prime))))"
                                                 ,
                                "                                 (mant prime))"
                                                 ,
                                   "                              (exp prime))]"
                                                 ,
                                                "            [(+ prime self)]))"
                                                 , "    (method * (prime) "
                                                 ,
          "        (mant:exp: Float (* mant (mant prime)) (+ exp (exp prime))))"
                                                 , "    (method reciprocal ()"
                                                 ,
                  "        (mant:exp: Float (div: 1000000000 mant) (- -9 exp)))"
                                                 ,
                              "    (method coerce: (aNumber) (asFloat aNumber))"
                                                 ,
                                                  "    (method asFloat () self)"
                                                 , "    (method asInteger ()"
                                                 , "        (if (< exp 0)"
                                                 ,
                 "            [(div: mant (raisedToInteger: 10 (negated exp)))]"
                                                 ,
                         "            [(*    mant (raisedToInteger: 10 exp))]))"
                                                 , "    (method asFraction ()"
                                                 , "        (if (< exp 0)"
                                                 ,
    "            [(num:den: Fraction mant (raisedToInteger: 10 (negated exp)))]"
                                                 ,
      "            [(num:den: Fraction (* mant (raisedToInteger: 10 exp)) 1)]))"
                                                 ,
                              "    (method negative         () (negative mant))"
                                                 ,
                              "    (method positive         () (positive mant))"
                                                 ,
                      "    (method strictlyPositive () (strictlyPositive mant))"
                                                 , "    (method print () "
                                                 ,
                                               "        (print-normalize self) "
                                                 ,
                                "        (print mant) (print #x10^) (print exp)"
                                                 , "        (normalize self))"
                                                 , ""
                                                 ,
                                                "    (method print-normalize ()"
                                                 ,
                      "        (while [(and: (< exp 0) [(= (mod: mant 10) 0)])]"
                                                 ,
                 "            [(set exp (+ exp 1)) (set mant (div: mant 10))]))"
                                                 , ")"
                                                 , "(class Collection Object"
                                                 , "  () ; abstract"
                                                 ,
                  "  (method do:     (aBlock)    (subclassResponsibility self))"
                                                 ,
                  "  (method add:    (newObject) (subclassResponsibility self))"
                                                 ,
                               "  (method remove:ifAbsent: (oldObject exnBlock)"
                                                 ,
                  "                              (subclassResponsibility self))"
                                                 ,
                  "  (method species ()          (subclassResponsibility self))"
                                                 ,
                                "  (class-method with: (anObject) (locals temp)"
                                                 , "      (set temp (new self))"
                                                 , "      (add: temp anObject)"
                                                 , "      temp)"
                                                 ,
                                                "  (method remove: (oldObject) "
                                                 ,
"      (remove:ifAbsent: self oldObject [(error: self #tried-to-remove-absent-object)]))"
                                                 ,
                                              "  (method addAll: (aCollection) "
                                                 ,
                             "      (do: aCollection (block (x) (add: self x)))"
                                                 , "      aCollection)"
                                                 ,
                                           "  (method removeAll: (aCollection) "
                                                 ,
                          "      (do: aCollection (block (x) (remove: self x)))"
                                                 , "      aCollection)"
                                                 ,
                                       "  (method isEmpty () (= (size self) 0))"
                                                 ,
                                               "  (method size () (locals temp)"
                                                 , "      (set temp 0)"
                                                 ,
                            "      (do: self (block (_) (set temp (+ temp 1))))"
                                                 , "      temp)"
                                                 ,
                             "  (method occurrencesOf: (anObject) (locals temp)"
                                                 , "      (set temp 0)"
                                                 , "      (do: self (block (x)"
                                                 ,
                   "         (ifTrue: (= x anObject) [(set temp (+ temp 1))])))"
                                                 , "      temp)"
                                                 ,
          "  (method includes: (anObject) (< 0 (occurrencesOf: self anObject)))"
                                                 , "  (method detect: (aBlock) "
                                                 ,
       "      (detect:ifNone: self aBlock [(error: self #no-object-detected)]))"
                                                 ,
          "  (method detect:ifNone: (aBlock exnBlock) (locals answer searching)"
                                                 , "      (set searching true)"
                                                 , "      (do: self (block (x)"
                                                 ,
                        "          (ifTrue: (and: searching [(value aBlock x)])"
                                                 ,
                                         "               [(set searching false)"
                                                 ,
                                            "                (set answer x)])))"
                                                 ,
                                       "      (if searching exnBlock [answer]))"
                                                 ,
                                "  (method inject:into: (thisValue binaryBlock)"
                                                 ,
   "     (do: self (block (x) (set thisValue (value binaryBlock x thisValue))))"
                                                 , "     thisValue)"
                                                 ,
                                      "  (method select: (aBlock) (locals temp)"
                                                 ,
                                          "     (set temp (new (species self)))"
                                                 ,
        "     (do: self (block (x) (ifTrue: (value aBlock x) [(add: temp x)])))"
                                                 , "     temp)"
                                                 , "  (method reject: (aBlock)"
                                                 ,
                       "     (select: self (block (x) (not (value aBlock x)))))"
                                                 ,
                                     "  (method collect: (aBlock) (locals temp)"
                                                 ,
                                          "     (set temp (new (species self)))"
                                                 ,
                      "     (do: self (block (x) (add: temp (value aBlock x))))"
                                                 , "     temp)"
                                                 ,
                                              "  (method asSet () (locals temp)"
                                                 , "       (set temp (new Set))"
                                                 ,
                                   "       (do: self (block (x) (add: temp x)))"
                                                 , "       temp)"
                                                 , "  (method print ()"
                                                 , "      (printName self)"
                                                 , "      (print lparen)"
                                                 ,
                          "      (do: self (block (x) (print space) (print x)))"
                                                 , "      (print space)"
                                                 , "      (print rparen)"
                                                 , "      self)"
                                                 ,
                                   "  (method printName () (print #Collection))"
                                                 , ")"
                                                 , "(class Set Collection"
                                                 ,
                                             "    (members)  ; list of elements"
                                                 ,
                               "    (class-method new () (initSet (new super)))"
                                                 ,
             "    (method initSet   () (set members (new List)) self) ; private"
                                                 ,
                                "    (method do: (aBlock) (do: members aBlock))"
                                                 ,
                                 "    (method remove:ifAbsent: (item exnBlock) "
                                                 ,
                             "        (remove:ifAbsent: members item exnBlock))"
                                                 , "    (method add: (item)"
                                                 ,
             "        (ifFalse: (includes: members item) [(add: members item)])"
                                                 , "        item)"
                                                 ,
                                                 "    (method species   () Set)"
                                                 ,
                                        "    (method printName () (print #Set))"
                                                 ,
                                                "    (method asSet     () self)"
                                                 , ")"
                                                 ,
                                             "(class KeyedCollection Collection"
                                                 , "    ()  ; abstract class"
                                                 ,
          "    (method at:put: (key value)       (subclassResponsibility self))"
                                                 ,
          "    (method associationsDo: (aBlock)  (subclassResponsibility self))"
                                                 , "    (method do: (aBlock) "
                                                 ,
          "        (associationsDo: self (block (x) (value aBlock (value x)))))"
                                                 , "    (method at: (key)    "
                                                 ,
               "        (at:ifAbsent: self key [(error: self #key-not-found)]))"
                                                 ,
                                      "    (method at:ifAbsent: (key exnBlock) "
                                                 ,
                             "        (value (associationAt:ifAbsent: self key "
                                                 ,
         "                   [(key:value: Association nil (value exnBlock))])))"
                                                 ,
                                               "    (method includesKey: (key) "
                                                 ,
        "        (isKindOf: (associationAt:ifAbsent: self key []) Association))"
                                                 ,
                                             "    (method associationAt: (key) "
                                                 ,
    "        (associationAt:ifAbsent: self key [(error: self #key-not-found)]))"
                                                 ,
       "    (method associationAt:ifAbsent: (key exnBlock) (locals finishBlock)"
                                                 ,
                                            "        (set finishBlock exnBlock)"
                                                 ,
                                     "        (associationsDo: self (block (x) "
                                                 ,
               "            (ifTrue: (= (key x) key) [(set finishBlock [x])])))"
                                                 ,
                                                  "        (value finishBlock))"
                                                 ,
                                              "    (method keyAtValue: (value) "
                                                 ,
   "        (keyAtValue:ifAbsent: self value [(error: self #value-not-found)]))"
                                                 ,
          "    (method keyAtValue:ifAbsent: (value aBlock) (locals finishBlock)"
                                                 ,
                                              "        (set finishBlock aBlock)"
                                                 ,
                                     "        (associationsDo: self (block (x) "
                                                 ,
     "            (ifTrue: (= (value x) value) [(set finishBlock [(key x)])])))"
                                                 ,
                                                  "        (value finishBlock))"
                                                 , ")"
                                                 , "(class Association Object "
                                                 , "   (key value)"
                                                 ,
             "   (class-method key:value: (a b) (setKey:value: (new self) a b))"
                                                 ,
      "   (method setKey:value: (x y) (set key x) (set value y) self) ; private"
                                                 , "   (method key    ()  key)"
                                                 ,
                                                  "   (method value  ()  value)"
                                                 ,
                                          "   (method key:   (x) (set key   x))"
                                                 ,
                                          "   (method value: (y) (set value y))"
                                                 , ")"
                                                 ,
                                             "(class Dictionary KeyedCollection"
                                                 ,
                                            "    (table) ; list of Associations"
                                                 ,
                   "    (class-method new ()      (initDictionary (new super)))"
                                                 ,
          "    (method initDictionary () (set table (new List)) self) ; private"
                                                 ,
                            "    (method printName ()      (print #Dictionary))"
                                                 ,
                                     "    (method species ()        Dictionary)"
                                                 ,
                      "    (method associationsDo: (aBlock) (do: table aBlock))"
                                                 ,
                            "    (method at:put: (key value) (locals tempassoc)"
                                                 ,
                 "        (set tempassoc (associationAt:ifAbsent: self key []))"
                                                 ,
                                                 "        (if (isNil tempassoc)"
                                                 ,
                "             [(add: table (key:value: Association key value))]"
                                                 ,
                                      "             [(value: tempassoc value)])"
                                                 , "        value)"
                                                 ,
          "    (method add: (_) (error: self #can't-just-add:-to-a-Dictionary))"
                                                 , ")"
                                                 ,
                                 "(class SequenceableCollection KeyedCollection"
                                                 , "    () ; abstract class"
                                                 ,
                        "    (method firstKey () (subclassResponsibility self))"
                                                 ,
                        "    (method lastKey  () (subclassResponsibility self))"
                                                 ,
                           "    (method last     () (at: self (lastKey  self)))"
                                                 ,
                           "    (method first    () (at: self (firstKey self)))"
                                                 ,
        "    (method at:ifAbsent: (index exnBlock) (locals current resultBlock)"
                                                 ,
                                            "        (set resultBlock exnBlock)"
                                                 ,
                                         "        (set current (firstKey self))"
                                                 ,
                                                  "        (do: self (block (v)"
                                                 ,
               "            (ifTrue: (= current index) [(set resultBlock [v])])"
                                                 ,
                                     "            (set current (+ current 1))))"
                                                 ,
                                                  "        (value resultBlock))"
                                                 , ")"
                                                 , "(class Cons Object"
                                                 , "    (car cdr)"
                                                 ,
                                             "    (method car ()           car)"
                                                 ,
                                             "    (method cdr ()           cdr)"
                                                 ,
                         "    (method car: (anObject)  (set car anObject) self)"
                                                 ,
                         "    (method cdr: (anObject)  (set cdr anObject) self)"
                                                 ,
                                             "    (method pred: (aCons)    nil)"
                                                 ,
                                    "    (method deleteAfter () (locals answer)"
                                                 ,
                                                "        (set answer (car cdr))"
                                                 ,
                                                "        (set cdr    (cdr cdr))"
                                                 , "        (pred: cdr self)"
                                                 , "        answer)"
                                                 ,
                                           "    (method insertAfter: (anObject)"
                                                 ,
                       "        (set cdr (car: (cdr: (new Cons) cdr) anObject))"
                                                 ,
                                                 "        (pred: (cdr cdr) cdr)"
                                                 , "        anObject)"
                                                 , "    (method do: (aBlock)"
                                                 , "        (value aBlock car)"
                                                 , "        (do: cdr aBlock))"
                                                 ,
               "    (method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)"
                                                 ,
                                               "        (if (value aBlock self)"
                                                 ,
                                              "            [(deleteAfter pred)]"
                                                 ,
       "            [(rejectOne:ifAbsent:withPred: cdr aBlock exnBlock self)]))"
                                                 , ")"
                                                 , "(class ListSentinel Cons"
                                                 , "    (pred)"
                                                 ,
                                 "    (method pred: (aCons)   (set pred aCons))"
                                                 ,
                                             "    (method pred  ()        pred)"
                                                 ,
                                      "    (class-method new ()    (locals tmp)"
                                                 ,
                                                 "        (set tmp (new super))"
                                                 , "        (pred: tmp tmp)"
                                                 , "        (cdr:  tmp tmp)"
                                                 , "        tmp)"
                                                 ,
                                                 "    (method do: (aBlock) nil)"
                                                 ,
               "    (method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)"
                                                 , "        (value exnBlock)))"
                                                 ,
                                            "(class List SequenceableCollection"
                                                 , "    (sentinel)"
                                                 ,
   "    (class-method new ()        (sentinel: (new super) (new ListSentinel)))"
                                                 ,
              "    (method sentinel: (s)       (set sentinel s) self) ; private"
                                                 ,
                  "    (method isEmpty   ()        (= sentinel (cdr sentinel)))"
                                                 ,
                        "    (method last      ()        (car (pred sentinel)))"
                                                 ,
                  "    (method do:       (aBlock)  (do: (cdr sentinel) aBlock))"
                                                 ,
                                         "    (method species   ()        List)"
                                                 ,
                                "    (method printName ()        (print #List))"
                                                 ,
           "    (method addLast:  (item)   (insertAfter: (pred sentinel) item))"
                                                 ,
                  "    (method addFirst: (item)   (insertAfter: sentinel item))"
                                                 ,
                          "    (method add: (item)        (addLast: self item))"
                                                 ,
                        "    (method removeFirst ()     (deleteAfter sentinel))"
                                                 ,
                             "    (method remove:ifAbsent: (oldObject exnBlock)"
                                                 ,
                                         "        (rejectOne:ifAbsent:withPred:"
                                                 , "            (cdr sentinel)"
                                                 ,
                                 "            (block (x) (= oldObject (car x)))"
                                                 , "            exnBlock"
                                                 , "            sentinel))"
                                                 , "    (method firstKey () 1)"
                                                 ,
                                          "    (method lastKey  () (size self))"
                                                 ,
                                    "    (method at:put: (n value) (locals tmp)"
                                                 ,
                                              "        (set tmp (cdr sentinel))"
                                                 ,
                                                "        (whileFalse: [(= n 1)]"
                                                 , "           [(set n (- n 1))"
                                                 ,
                                             "            (set tmp (cdr tmp))])"
                                                 , "        (car: tmp value))"
                                                 , ")"
                                                 ,
                                           "(class Array SequenceableCollection"
                                                 ,
                                          "    () ; representation is primitive"
                                                 ,
                                   "    (class-method new: primitive arrayNew:)"
                                                 ,
      "    (class-method new () (error: self #size-of-Array-must-be-specified))"
                                                 ,
                                    "    (method size      primitive arraySize)"
                                                 ,
                                     "    (method at:       primitive arrayAt:)"
                                                 ,
                                 "    (method at:put:   primitive arrayAt:Put:)"
                                                 ,
                                               "    (method species   () Array)"
                                                 ,
                "    (method printName () nil) ; names of arrays aren't printed"
                                                 ,
                     "    (method add:             (x)   (fixedSizeError self))"
                                                 ,
                     "    (method remove:ifAbsent: (x b) (fixedSizeError self))"
                                                 ,
     "    (method fixedSizeError   ()    (error: self #arrays-have-fixed-size))"
                                                 ,
     "    (method select:  (_) (error: self #select-on-arrays-not-implemented))"
                                                 ,
    "    (method collect: (_) (error: self #collect-on-arrays-not-implemented))"
                                                 , "    (method firstKey () 1)"
                                                 ,
                                          "    (method lastKey  () (size self))"
                                                 ,
                                       "    (method do: (aBlock) (locals index)"
                                                 ,
                                           "        (set index (firstKey self))"
                                                 ,
                                             "        (timesRepeat: (size self)"
                                                 ,
                                   "           [(value aBlock (at: self index))"
                                                 ,
                                        "            (set index (+ index 1))]))"
                                                 , ")"
                                                  ])
  in  readEvalPrint
        ( defs : def stream
        , echoBasis
        , fn s => app print ["error in initial basis: ", s, "\n"]
        )
        initialXi
  end
(* initialization ((usm)) 495b *)
local 
  fun newInstance classname = SEND (nullsrc, "new", VAR classname, [])
in
  val initialXi = evaldef (VAL ("true",  newInstance "True" ), false, initialXi)
  val initialXi = evaldef (VAL ("false", newInstance "False"), false, initialXi)
end
(* initialization ((usm)) 495c *)
val _ =
  ( closeLiteralsCycle initialXi
  ; closeBooleansCycle initialXi
  ; closeBlocksCycle   initialXi
  ) handle NotFound n =>
      ( app print ["Fatal error: ", n, " is not defined in the initial basis\n"]
      ; raise InternalError "this can't happen"
      )
  | e => ( print "Error binding basis classes into interpreter\n"; raise e)
(* initialization ((usm)) 496a *)
fun addVal ((name, v), xi) = evaldef (VAL (name, VALUE v), false, xi)
val initialXi = foldl addVal initialXi
  [ ("nil", nilValue)
  , ("lparen",  mkSymbol "("),  ("rparen", mkSymbol ")")
  , ("lbrack",  mkSymbol "["),  ("rbrack", mkSymbol "]")
  , ("newline", mkSymbol "\n"), ("space",  mkSymbol " ")
  ]
(* initialization ((usm)) 496b *)
fun runInterpreter noisy = 
  let val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader smalltalkSyntax prompts ("standard input", streamOfLines
                                                                   TextIO.stdIn)
      fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
  in  ignore (readEvalPrint (defs : def stream, true, errorln) initialXi)
  end 
(* type declarations for consistency checking *)
val _ = op runInterpreter : bool -> unit


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
