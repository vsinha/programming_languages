(* mlscheme.sml 224 *)


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
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values ((mlscheme)) 215 *)
datatype exp = LITERAL of value
             | VAR     of name
             | SET     of name * exp
             | IFX     of exp * exp * exp
             | WHILEX  of exp * exp
             | BEGIN   of exp list
             | APPLY   of exp * exp list
             | LETX    of let_kind * (name * exp) list * exp
             | LAMBDA  of lambda
and let_kind = LET | LETREC | LETSTAR
and    value = NIL
             | BOOL      of bool   
             | NUM       of int
             | SYM       of name
             | PAIR      of value * value
             | CLOSURE   of lambda * value ref env
             | PRIMITIVE of primitive
withtype primitive = value list -> value (* raises RuntimeError *)
     and lambda    = name list * exp

exception RuntimeError of string (* error message *)
(* abstract syntax and values ((mlscheme)) 216a *)
datatype def = VAL    of name * exp
             | EXP    of exp
             | DEFINE of name * lambda
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
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* parsing ((mlscheme)) 673a *)
val name    = (fn (NAME  n) => SOME n  | _ => NONE) <$>? token
val booltok = (fn (SHARP b) => SOME b  | _ => NONE) <$>? token
val int     = (fn (INT   n) => SOME n  | _ => NONE) <$>? token
val quote   = (fn (QUOTE)   => SOME () | _ => NONE) <$>? token
(* parsing ((mlscheme)) 673b *)
fun sexp tokens = (
     SYM          <$> (notDot <$>! name)
 <|> NUM          <$> int
 <|> BOOL         <$> booltok
 <|> embedList    <$> "(" >-- many sexp --< ")"
 <|> (fn v => embedList [SYM "quote", v]) 
                  <$> (quote *> sexp)
) tokens
and notDot "." = ERROR
                      "this interpreter cannot handle . in quoted S-expressions"
  | notDot s   = OK s
(* type declarations for consistency checking *)
val _ = op sexp : value parser
(* parsing ((mlscheme)) 673c *)
val formals = 
  "(" >-- many name --< ")"
fun lambda xs exp =
  nodups ("formal parameter", "lambda") xs >>=+ (fn xs => LAMBDA (xs, exp))
(* type declarations for consistency checking *)
val _ = op formals : name list parser
val _ = op lambda  : name list located -> exp -> exp error
(* parsing ((mlscheme)) 673d *)
local
  fun letDups LETSTAR (loc, bindings) = OK bindings
    | letDups kind    (loc, bindings) =
        let val names    = map (fn (n, _) => n) bindings
            val kindName = case kind of LET => "let" | LETREC => "letrec" | _ =>
                                                                            "??"
        in  nodups ("bound name", kindName) (loc, names) >>=+ (fn _ => bindings)
        end
in
  fun letx kind bs exp = letDups kind bs >>=+ (fn bs => LETX (kind, bs, exp))
end
(* type declarations for consistency checking *)
val _ = op letx : let_kind -> (name * exp) list located -> exp -> exp error
(* parsing ((mlscheme)) 674a *)
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
 <|> br "lambda" "(lambda (names) body)"    (       lambda  <$> @@ formals  <*>!
                                                                            exp)
 <|> br "let"    "(let (bindings) body)"    (letx   LET     <$> @@ bindings <*>!
                                                                            exp)
 <|> br "letrec" "(letrec (bindings) body)" (letx   LETREC  <$> @@ bindings <*>!
                                                                            exp)
 <|> br "let*"   "(let* (bindings) body)"   (letx   LETSTAR <$> @@ bindings <*>!
                                                                            exp)
 <|> "(" >-- literal ")" <!> "empty application"
 <|> curry APPLY <$> "(" >-- exp <*> many exp --< ")"
) tokens
and bindings ts = ("(" >-- (many binding --< ")" <?> "(x e)...")) ts
and binding  ts = ("(" >-- (pair <$> name <*> exp --< ")" <?>
                                                        "(x e) in bindings")) ts
(* type declarations for consistency checking *)
val _ = op exp      : exp parser
val _ = op bindings : (name * exp) list parser
(* parsing ((mlscheme)) 674b *)
fun dfn f formals body =
  nodups ("formal parameter", "definition of function " ^ f) formals >>=+
  (fn xs => DEFINE (f, (xs, body)))
(* type declarations for consistency checking *)
val _ = op dfn : name -> name list located -> exp -> def error
(* parsing ((mlscheme)) 674c *)
val def = 
     bracket "define" "(define f (args) body)" (dfn <$> name <*> @@ formals <*>!
                                                                            exp)
 <|> bracket "val"    "(val x e)"              (curry VAL <$> name <*> exp)
 <|> bracket "use"    "(use filename)"         (USE       <$> name)
 <|> literal ")" <!> "unexpected right parenthesis"
 <|> EXP <$> exp
 <?> "definition"
(* type declarations for consistency checking *)
val _ = op def : def parser
(* parsing ((mlscheme)) 674d *)
val schemeSyntax = (schemeToken, def)
(* type declarations for consistency checking *)
val _ = op schemeSyntax : token lexer * def parser


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
(*   EVALUATION                                                  *)
(*                                                               *)
(*****************************************************************)

(* evaluation ((mlscheme)) 217b *)
(* definition of [[separate]] 218d *)
fun separate (zero, sep) =  (* print list with separator *)
  let fun s []     = zero
        | s [x]    = x
        | s (h::t) = h ^ sep ^ s t
  in  s
end
val spaceSep = separate ("", " ")  (* print separated by spaces *)
fun eval (e, rho) =
  let fun ev (LITERAL n) = n
        (* more alternatives for [[ev]] ((mlscheme)) 217c *)
        | ev (VAR v) = !(find(v, rho))
        | ev (SET (n, e)) = 
            let val v = ev e
            in  find (n, rho) := v;
                v
            end
        (* more alternatives for [[ev]] ((mlscheme)) 218a *)
        | ev (IFX (e1, e2, e3)) = ev (if bool (ev e1) then e2 else e3)
        | ev (WHILEX (guard, body)) = 
            if bool (ev guard) then 
              (ev body; ev (WHILEX (guard, body)))
            else
              NIL
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, BOOL false)
            end
        (* more alternatives for [[ev]] ((mlscheme)) 218b *)
        | ev (LAMBDA l) = CLOSURE (l, rho)
        | ev (APPLY (f, args))  = 
               (case ev f
                  of PRIMITIVE prim => prim (map ev args)
                   | CLOSURE clo    => (* apply closure [[clo]] to [[args]] ((
                                                              mlscheme)) 218c *)
                                       let val ((formals, body), savedrho) = clo
                                           val actuals = map ev args
                                       in  eval (body, bindList (formals, map
                                                         ref actuals, savedrho))
                                           handle BindListLength => 
                                               raise RuntimeError (
                                      "Wrong number of arguments to closure; " ^
                                                                   "expected ("
                                                       ^ spaceSep formals ^ ")")
                                       end
                   | v => raise RuntimeError ("Applied non-function " ^
                                                                  valueString v)
               )
        (* more alternatives for [[ev]] ((mlscheme)) 219a *)
        | ev (LETX (LET, bs, body)) =
            let val (names, values) = ListPair.unzip bs
        (* type declarations for consistency checking *)
        val _ = ListPair.unzip : ('a * 'b) list -> 'a list * 'b list
            in  eval (body, bindList (names, map (ref o ev) values, rho))
            end
        | ev (LETX (LETSTAR, bs, body)) =
            let fun step ((n, e), rho) = bind (n, ref (eval (e, rho)), rho)
            in  eval (body, foldl step rho bs)
            end
        | ev (LETX (LETREC, bs, body)) =
            let val (names, values) = ListPair.unzip bs
                val rho' = bindList (names, map (fn _ => ref NIL) values, rho)
                val bs = map (fn (n, e) => (n, eval (e, rho'))) bs
            in  List.app (fn (n, v) => find (n, rho') := v) bs; 
                eval (body, rho')
            end
  in  ev e
  end
(* type declarations for consistency checking *)
val _ = op eval : exp * value ref env -> value
(* evaluation ((mlscheme)) 219b *)
fun arityError n args =
  raise RuntimeError ("primitive function expected " ^ Int.toString n ^
                      "arguments; got " ^ Int.toString (length args))
fun binaryOp f = (fn [a, b] => f (a, b) | args => arityError 2 args)
fun unaryOp  f = (fn [a]    => f a      | args => arityError 1 args)
(* type declarations for consistency checking *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* evaluation ((mlscheme)) 219c *)
fun arithOp f = binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                           | _ => raise RuntimeError "integers expected")
(* type declarations for consistency checking *)
val _ = op arithOp: (int * int -> int) -> (value list -> value)
(* evaluation ((mlscheme)) 220b *)
fun predOp f     = unaryOp  (embedPredicate f)
fun comparison f = binaryOp (embedPredicate f)
fun intcompare f = comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                                | _ => raise RuntimeError "integers expected")
(* type declarations for consistency checking *)
val _ = op predOp     : (value         -> bool) -> (value list -> value)
val _ = op comparison : (value * value -> bool) -> (value list -> value)
val _ = op intcompare : (int   * int   -> bool) -> (value list -> value)
(* evaluation ((mlscheme)) 221b *)
fun evaldef (d, rho, echo) =
  let (* definitions of [[addName]] and [[showVal]] 221c *)
      fun addName (name, rho) = (find (name, rho); rho)
                                handle NotFound _ => bind (name, ref NIL, rho)
      fun showVal name (LAMBDA _) _ = name
        | showVal name _          v = valueString v
(* type declarations for consistency checking *)
val _ = op evaldef : def  * value ref env * (string->unit) -> value ref env
val _ = op addName : name * value ref env                  -> value ref env
val _ = op showVal : name -> exp -> value -> string
  in  case d
        of VAL (name, e)         => let val rho = addName (name, rho)
                                        val v   = eval (e, rho)
                                    in  ( find (name, rho) := v
                                        ; echo (showVal name e v)
                                        ; rho
                                        )
                                    end
         | EXP e                 => let val v   = eval (e, rho)
                                        val rho = addName ("it", rho)
                                    in  ( find ("it", rho) := v
                                        ; echo (valueString v)
                                        ; rho
                                        )
                                    end
         | DEFINE (name, lambda) => evaldef (VAL (name, LAMBDA lambda), rho,
                                                                           echo)
         | USE filename          => use readEvalPrint schemeSyntax filename rho
  end
(* evaluation ((mlscheme)) 222b *)
and readEvalPrint (defs, echo, errmsg) rho =
  let fun processDef (def, rho) =
            let fun continue msg = (errmsg msg; rho)
            in  evaldef (def, rho, echo)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* more read-eval-print handlers 222c *)
                (* more read-eval-print handlers 223a *)
                | Div               => continue "Division by zero"
                | Overflow          => continue "Arithmetic overflow"
                | RuntimeError msg  => continue ("run-time error: " ^ msg)
                | NotFound n        => continue ("variable " ^ n ^ " not found")
            end
  in  streamFold processDef rho defs
  end
(* type declarations for consistency checking *)
val _ = op readEvalPrint : def stream * (string->unit) * (string->unit) -> value
                                                        ref env -> value ref env


(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION                                              *)
(*                                                               *)
(*****************************************************************)

(* initialization ((mlscheme)) 223b *)
fun initialEnv () =
  let val rho =
        foldl (fn ((name, prim), rho) => bind (name, ref (PRIMITIVE prim), rho))
              emptyEnv ((* primitives [[::]] ((mlscheme)) 220a *)
                        ("+", arithOp op +  ) :: 
                        ("-", arithOp op -  ) :: 
                        ("*", arithOp op *  ) :: 
                        ("/", arithOp op div) ::
                        (* primitives [[::]] ((mlscheme)) 220c *)
                        ("<", intcompare op <) :: 
                        (">", intcompare op >) ::
                        ("=", comparison (fn (NIL,     NIL    ) => true
                                           | (NUM  n1, NUM  n2) => n1 = n2
                                           | (SYM  v1, SYM  v2) => v1 = v2
                                           | (BOOL b1, BOOL b2) => b1 = b2
                                           |  _                 => false)) ::
                        ("null?",    predOp (fn (NIL   ) => true | _ => false))
                                                                              ::
                        ("boolean?", predOp (fn (BOOL _) => true | _ => false))
                                                                              ::
                        ("number?",  predOp (fn (NUM  _) => true | _ => false))
                                                                              ::
                        ("symbol?",  predOp (fn (SYM  _) => true | _ => false))
                                                                              ::
                        ("pair?",    predOp (fn (PAIR _) => true | _ => false))
                                                                              ::
                        ("procedure?",
                                     predOp (fn (PRIMITIVE _) => true | (CLOSURE
                                                    _) => true | _ => false)) ::
                        (* primitives [[::]] ((mlscheme)) 220d *)
                        ("cons", binaryOp (fn (a, b) => PAIR (a, b))) ::
                        ("car",  unaryOp  (fn (PAIR (car, _)) => car 
                                            | v => raise RuntimeError
                                                           (
                                "car applied to non-list " ^ valueString v))) ::
                        ("cdr",  unaryOp  (fn (PAIR (_, cdr)) => cdr 
                                            | v => raise RuntimeError
                                                           (
                                "cdr applied to non-list " ^ valueString v))) ::
                        (* primitives [[::]] ((mlscheme)) 221a *)
                        ("print", unaryOp (fn v => (print (valueString v^"\n");
                                                                      v)))    ::
                        ("error", unaryOp (fn v => raise RuntimeError (
                                                        valueString v))) :: nil)
      val basis  = (* ML representation of initial basis (generated by a script)
                                                                              *)

                    [ "(define caar (xs) (car (car xs)))"
                    , "(define cadr (xs) (car (cdr xs)))"
                    , "(define cdar (xs) (cdr (car xs)))"
                    , "(define list1 (x)     (cons x '()))"
                    , "(define list2 (x y)   (cons x (list1 y)))"
                    , "(define list3 (x y z) (cons x (list2 y z)))"
                    , "(define length (xs)"
                    , "  (if (null? xs) 0"
                    , "    (+ 1 (length (cdr xs)))))"
                    , "(define and (b c) (if b  c  b))"
                    , "(define or  (b c) (if b  b  c))"
                    , "(define not (b)   (if b #f #t))"
                    ,
"(define atom? (x) (or (number? x) (or (symbol? x) (or (boolean? x) (null? x)))))"
                    , "(define equal? (s1 s2)"
                    , "  (if (or (atom? s1) (atom? s2))"
                    , "    (= s1 s2)"
                    ,
             "    (and (equal? (car s1) (car s2)) (equal? (cdr s1) (cdr s2)))))"
                    , "(define append (xs ys)"
                    , "  (if (null? xs)"
                    , "     ys"
                    , "     (cons (car xs) (append (cdr xs) ys))))"
                    , "(define revapp (xs ys)"
                    , "  (if (null? xs)"
                    , "     ys"
                    , "     (revapp (cdr xs) (cons (car xs) ys))))"
                    , "(define reverse (xs) (revapp xs '()))"
                    , "(define mk-alist-pair (k a) (list2 k a))"
                    , "(define alist-pair-key        (pair)  (car  pair))"
                    , "(define alist-pair-attribute  (pair)  (cadr pair))"
                    ,
     "(define alist-first-key       (alist) (alist-pair-key       (car alist)))"
                    ,
     "(define alist-first-attribute (alist) (alist-pair-attribute (car alist)))"
                    , "(define bind (k a alist)"
                    , "  (if (null? alist)"
                    , "    (list1 (mk-alist-pair k a))"
                    , "    (if (equal? k (alist-first-key alist))"
                    , "      (cons (mk-alist-pair k a) (cdr alist))"
                    , "      (cons (car alist) (bind k a (cdr alist))))))"
                    , "(define find (k alist)"
                    , "  (if (null? alist) '()"
                    , "    (if (equal? k (alist-first-key alist))"
                    , "      (alist-first-attribute alist)"
                    , "      (find k (cdr alist)))))"
                    , "(define o (f g) (lambda (x) (f (g x))))"
                    , "(define curry   (f) (lambda (x) (lambda (y) (f x y))))"
                    , "(define uncurry (f) (lambda (x y) ((f x) y)))"
                    , "(define filter (p? xs)"
                    , "  (if (null? xs)"
                    , "    '()"
                    , "    (if (p? (car xs))"
                    , "      (cons (car xs) (filter p? (cdr xs)))"
                    , "      (filter p? (cdr xs)))))"
                    , "(define map (f xs)"
                    , "  (if (null? xs)"
                    , "    '()"
                    , "    (cons (f (car xs)) (map f (cdr xs)))))"
                    , "(define exists? (p? xs)"
                    , "  (if (null? xs)"
                    , "    #f"
                    , "    (if (p? (car xs)) "
                    , "      #t"
                    , "      (exists? p? (cdr xs)))))"
                    , "(define all? (p? xs)"
                    , "  (if (null? xs)"
                    , "    #t"
                    , "    (if (p? (car xs))"
                    , "      (all? p? (cdr xs))"
                    , "      #f)))"
                    , "(define foldr (op zero xs)"
                    , "  (if (null? xs)"
                    , "    zero"
                    , "    (op (car xs) (foldr op zero (cdr xs)))))"
                    , "(define foldl (op zero xs)"
                    , "  (if (null? xs)"
                    , "    zero"
                    , "    (foldl op (op (car xs) zero) (cdr xs))))"
                    , "(define <= (x y) (not (> x y)))"
                    , "(define >= (x y) (not (< x y)))"
                    , "(define != (x y) (not (= x y)))"
                    , "(define max (x y) (if (> x y) x y))"
                    , "(define min (x y) (if (< x y) x y))"
                    , "(define mod (m n) (- m (* n (/ m n))))"
                    , "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))"
                    , "(define lcm (m n) (if (= m 0) 0 (* m (/ n (gcd m n)))))"
                    , "(define caar  (sx) (car (car  sx)))"
                    , "(define cdar  (sx) (cdr (car  sx)))"
                    , "(define cadr  (sx) (car (cdr  sx)))"
                    , "(define cddr  (sx) (cdr (cdr  sx)))"
                    , "(define caaar (sx) (car (caar sx)))"
                    , "(define cdaar (sx) (cdr (caar sx)))"
                    , "(define caadr (sx) (car (cadr sx)))"
                    , "(define cdadr (sx) (cdr (cadr sx)))"
                    , "(define cadar (sx) (car (cdar sx)))"
                    , "(define cddar (sx) (cdr (cdar sx)))"
                    , "(define caddr (sx) (car (cddr sx)))"
                    , "(define cdddr (sx) (cdr (cddr sx)))"
                    , "(define list1 (x)               (cons x '()))"
                    , "(define list2 (x y)             (cons x (list1 y)))"
                    , "(define list3 (x y z)           (cons x (list2 y z)))"
                    , "(define list4 (x y z a)         (cons x (list3 y z a)))"
                    ,
                     "(define list5 (x y z a b)       (cons x (list4 y z a b)))"
                    ,
                   "(define list6 (x y z a b c)     (cons x (list5 y z a b c)))"
                    ,
                 "(define list7 (x y z a b c d)   (cons x (list6 y z a b c d)))"
                    ,
               "(define list8 (x y z a b c d e) (cons x (list7 y z a b c d e)))"
                     ]
      val defs = reader schemeSyntax noPrompts ("initial basis", streamOfList
                                                                          basis)
  in  readEvalPrint (defs, fn _ => (), fn _ => ()) rho
  end
(* initialization ((mlscheme)) 223c *)
fun runInterpreter noisy = 
  let val rho = initialEnv ()
      fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader schemeSyntax prompts ("standard input", streamOfLines
                                                                   TextIO.stdIn)
  in  ignore (readEvalPrint (defs, writeln, errorln) rho)
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
