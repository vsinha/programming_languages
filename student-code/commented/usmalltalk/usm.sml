(* The code in the interpreter is organized so that the *)
(* [[]] is as early as                          *)
(* possible, immediately following the definition of *)
(* [[]]. Afterward come                         *)
(* parsing, primitives, and evaluation. The code for *)
(* [[]] comes almost at the                     *)
(* end, just before the execution of the command line. *)
(* The full structure of the interpreter is as follows: *)
(* <usm.sml>=                                   *)


(*****************************************************************)
(*                                                               *)
(*   ENVIRONMENTS                                                *)
(*                                                               *)
(*****************************************************************)

(* <environments>=                              *)
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
(* We represent an environment of type [['a env]] as a *)
(* list of ([[name]], [['a]]) pairs. The declarations in *)
(* the box give the interface to our implementation; *)
(* through some Noweb hackery, they are checked by the *)
(* ML compiler.                                 *)
(* <boxed values 21>=                           *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* Because ML strings are immutable, we can use them to *)
(* represent names directly. We also use exceptions, not *)
(* an [[error]] procedure, to indicate when things have *)
(* gone wrong. The exceptions we use are listed in *)
(* Table [->].                                  *)



(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS                                            *)
(*                                                               *)
(*****************************************************************)

(* A source-code location includes a name for the *)
(* source, plus line number.                    *)
(* <lexical analysis ((usm))>=                  *)
type srcloc = string * int
val nullsrc = ("internally generated SEND node", 1)
fun srclocString (source, line) = source ^ ", line " ^ Int.toString line
(* The representation of a token is almost the same as *)
(* in micro-Scheme. The differences are that there are *)
(* two kinds of brackets, and that a [[#]] character *)
(* does not introduce a Boolean.                *)
(* <lexical analysis ((usm))>=                  *)
datatype token = INT     of int
               | NAME    of name
               | BRACKET of char          (* ( or ) or [ or ] *)
               | SHARP   of string option (* symbol or array *)
(* To produce error messages, we must be able to convert *)
(* a token back to a string.                    *)
(* <lexical analysis ((usm))>=                  *)
fun tokenString (INT     n)      = Int.toString n
  | tokenString (NAME    x)      = x
  | tokenString (BRACKET c)      = str c
  | tokenString (SHARP NONE)     = "#"
  | tokenString (SHARP (SOME s)) = "#" ^ s
(* <lexical analysis ((usm))>=                  *)
fun isLiteral s token = 
  case (s, token) of ("#", SHARP NONE) => true
                   | (s,   NAME s' )   => s = s'
                   | (s,   BRACKET c)  => s = str c
                   | _ => false
(* This appendix presents all the abstractions I use to *)
(* build interactive parsers:                   *)
(*                                              *)
(*   * Lazy streams, which are themselves based on *)
(*  suspensions                                 *)
(*   * The error monad, which tracks parsing errors and *)
(*  enables parsers to recover                  *)
(*   * Parsing combinators, which help turn sequences *)
(*  into tokens or syntax                       *)
(*   * A reader, which ties everything together. *)
(*                                              *)
(* These abstractions are coded in a number of different *)
(* parts:                                       *)
(* <support for streams, lexical analysis, and parsing>= *)
(* <suspensions>=                               *)
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
(* <boxed values 35>=                           *)
val _ = op delay : (unit -> 'a) -> 'a susp
val _ = op force : 'a susp -> 'a
(* Stream representation and basic functions    *)
(*                                              *)
(* My representation of streams uses three cases: [There *)
(* are simpler representations; this one has the merit *)
(* that one can define a polymorphic empty stream *)
(* without running afoul of the value restriction.] *)
(*                                              *)
(*   * The [[EOS]] constructor represents an empty *)
(*  stream.                                     *)
(*   * The [[:::]] constructor (pronounced ``cons''), *)
(*  which I intend should remind you of ML's [[::]] *)
(*  constructor for lists, represents a stream in *)
(*  which an action has already been taken, and the *)
(*  first element of the stream is available (as are *)
(*  the remaining elements). Like the standard [[::]] *)
(*  constructor, the [[:::]] is infix.          *)
(*   * The [[SUSPENDED]] constructor represents a stream *)
(*  in which the action need to produce the next *)
(*  element may not have been taken yet. Getting the *)
(*  element will require forcing the suspension, and *)
(*  if the action in the suspension is pending, it *)
(*  will be taken at that time.                 *)
(*                                              *)
(* <streams>=                                   *)
datatype 'a stream 
  = EOS
  | :::       of 'a * 'a stream
  | SUSPENDED of 'a stream susp
infixr 3 :::
(* Even though its representation uses mutable state *)
(* (the suspension), the stream is an immutable *)
(* abstraction. [To~help with debugging, I~sometimes *)
(* violate the abstraction and look at the state of a *)
(* [[SUSPENDED]] stream.] To observe that abstraction, *)
(* call [[streamGet]]. This function performs whatever *)
(* actions are needed either to produce a pair holding *)
(* an element an a stream (represented as \monoSOME (x, *)
(* xs) or to decide that the stream is empty and no more *)
(* elements can be produced (represented as [[NONE]]). *)

(* <streams>=                                   *)
fun streamGet EOS = NONE
  | streamGet (x ::: xs)    = SOME (x, xs)
  | streamGet (SUSPENDED s) = streamGet (force s)
(* <streams>=                                   *)
fun streamOfList xs = 
  foldr (op :::) EOS xs
(* <boxed values 36>=                           *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a streams is read, no new actions are performed. *)
(* <boxed values 36>=                           *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* <boxed values 37>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such stream, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 37>=                           *)
val _ = op delayedStream : (unit -> 'a stream) -> 'a stream
(* <streams>=                                   *)
fun streamOfEffects next =
  delayedStream (fn () => case next () of NONE => EOS
                                        | SOME a => a ::: streamOfEffects next)
(* Creating streams using actions and functions *)
(*                                              *)
(* Function [[streamOfEffects]] produces the stream of *)
(* results obtained by repeatedly performing a single *)
(* action (like reading a line of input). The action has *)
(* type [[unit -> 'a option]], and the stream performs *)
(* the action repeatedly until it returns [[NONE]]. *)
(* <boxed values 38>=                           *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* <streams>=                                   *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 39>=                           *)
type line = line
val _ = op streamOfLines : TextIO.instream -> line stream
(* <streams>=                                   *)
fun streamRepeat x =
  delayedStream (fn () => x ::: streamRepeat x)
(* Where [[streamOfEffects]] produces the results of *)
(* repeating a single action again and again,   *)
(* [[streamRepeat]] simply repeats a single value again *)
(* and again. This operation might sound useless, but *)
(* here's an example: suppose we read a sequence of *)
(* lines from a file, and for error reporting, we want *)
(* to tag each line with its source location, i.e., file *)
(* name and line number. Well, the file names are all *)
(* the same, and one easy way to associate the same file *)
(* name with every line is to repeat the file name *)
(* indefinitely, then join the two streams. Function *)
(* [[streamRepeat]] creates an infinite stream that *)
(* repeats a value of any type:                 *)
(* <boxed values 40>=                           *)
val _ = op streamRepeat : 'a -> 'a stream
(* <streams>=                                   *)
fun streamOfUnfold next state =
  delayedStream (fn () => case next state
                            of NONE => EOS
                             | SOME (a, state) => a ::: streamOfUnfold next
                                                                          state)
(* A more sophisticated way to produce a stream is to *)
(* use a function that depends on an evolving state of *)
(* some unknown type [['b]]. The function is applied to *)
(* a state (of type [['b]]) and may produce a pair *)
(* containing a value of type [['a]] and a new state. *)
(* By repeatedly applying the function, we produce a *)
(* sequence of results of type [['a]]. This operation, *)
(* in which a function is used to expand a value into a *)
(* sequence, is the dual of the fold operation, which is *)
(* used to collapse a sequence into a value. The new *)
(* operation is therefore called unfold.        *)
(* <boxed values 41>=                           *)
val _ = op streamOfUnfold : ('b -> ('a * 'b) option) -> 'b -> 'a stream
(* Function [[streamOfUnfold]] can turn any ``get'' *)
(* function into a stream. In fact, the standard unfold *)
(* and get operations should obey the following *)
(* algebraic law:                               *)
(*                                              *)
(*  streamOfUnfold streamGet xs ===xs.          *)
(*                                              *)
(* Another useful ``get'' function is [[(fn n => SOME *)
(* (n, n+1))]]; passing this function to        *)
(* [[streamOfUnfold]] results in an infinite stream of *)
(* increasing integers.                         *)

(* <streams>=                                   *)
fun preStream (pre, xs) = 
  streamOfUnfold (fn xs => (pre (); streamGet xs)) xs
(* It's also useful to be able to perform an action *)
(* immediately after getting an element from a stream. *)
(* In [[postStream]], I perform the action only if the *)
(* [[streamGet]] operation is successful. That way, the *)
(* [[post]] action has access to the element that has *)
(* been gotten. Post-get actions are especially useful *)
(* for debugging.                               *)

(* <streams>=                                   *)
fun postStream (xs, post) =
  streamOfUnfold (fn xs => case streamGet xs
                             of NONE => NONE
                              | head as SOME (x, _) => (post x; head)) xs
(* Given an action called [[pre]] and a stream xs, *)
(* I define a stream \monopreStream (pre, xs) that adds *)
(* [[pre ()]] to the action performed by the stream. *)
(* Roughly speaking,                            *)
(*                                              *)
(*  \monostreamGet (preStream (pre, xs)) = \mono(pre *)
(*  (); streamGet xs).                          *)
(*                                              *)
(* (The equivalence is only rough because the pre action *)
(* is performed only when an action is needed to get a *)
(* value from xs.)                              *)
(* <boxed values 42>=                           *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* <boxed values 42>=                           *)
val _ = op postStream : 'a stream * ('a -> unit) -> 'a stream
(* <streams>=                                   *)
fun streamMap f xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => f x ::: streamMap f xs)
(* Standard list functions ported to streams    *)
(*                                              *)
(* Functions like [[map]], [[filter]], [[fold]], *)
(* [[zip]], and [[concat]] are every bit as useful on *)
(* streams as they are on lists. streams.       *)
(* <boxed values 43>=                           *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 44>=                           *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right: [*]                                   *)
(* <boxed values 45>=                           *)
val _ = op streamFold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b

(* <streams>=                                   *)
fun streamZip (xs, ys) =
  delayedStream
  (fn () => case (streamGet xs, streamGet ys)
              of (SOME (x, xs), SOME (y, ys)) => (x, y) ::: streamZip (xs, ys)
               | _ => EOS)
(* <streams>=                                   *)
fun streamConcat xss =
  let fun get (xs, xss) =
        case streamGet xs
          of SOME (x, xs) => SOME (x, (xs, xss))
           | NONE => case streamGet xss
                       of SOME (xs, xss) => get (xs, xss)
                        | NONE => NONE
  in  streamOfUnfold get (EOS, xss)
  end
(* Function [[streamZip]] returns a stream that is as *)
(* long as the shorter of the two argument streams. *)
(* In particular, if [[streamZip]] is applied to a *)
(* finite stream and an infinite stream, the result is a *)
(* finite stream.                               *)
(* <boxed values 46>=                           *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 46>=                           *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 47>=                           *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 48>=                           *)
val _ = op @@@ : 'a stream * 'a stream -> 'a stream
(* A function that's guaranteed always to produce a *)
(* result of type [['a]] simply returns such a result. *)
(* A function that might produce a result of type [['a]] *)
(* or might detect an error returns a result of type *)
(* [['a error]]. The result contains either a value of *)
(* type [['a]] or an error message.             *)
(* <error handling>=                            *)
datatype 'a error = OK of 'a | ERROR of string
(* <error handling>=                            *)
infix 1 >>=
fun (OK x)      >>= k  =  k x
  | (ERROR msg) >>= k  =  ERROR msg
(* How do we compose error-detecting functions? That is, *)
(* how to we write [[g (f x)]] in the case where either *)
(* [[f]] or [[g]] might detect an error? The standard *)
(* technique is to define a sequencing operator written *)
(* [[>>=]], which uses a special form of        *)
(* continuation-passing style. (The traditional name of *)
(* the [[>>=]] operator is ``bind,'' but you might wish *)
(* to pronounce it ``and then.'') The idea is that we *)
(* apply [[f]] to [[x]], and if the result is [[OK y]], *)
(* we can then continue by applying [[g]] to [[y]]. But *)
(* if the result of applying [[(f x)]] is an error, that *)
(* error is the result of the whole computation. The *)
(* [[>>=]] operator sequences the possibly erroneous *)
(* result [[(f x)]] with the continuation [[g]], thus *)
(*                                              *)
(*  [[f x >>= g]]                               *)
(*                                              *)
(* In the definition, I write the second function as  *)
(* [[k]], not [[g]], because [[k]] is the traditional *)
(* letter for a continuation.                   *)
(* <boxed values 49>=                           *)
val _ = op >>= : 'a error * ('a -> 'b error) -> 'b error
(* A very common special case occurs when the   *)
(* continuation always succeeds. That is, the idea is *)
(* that if [[(f x)]] succeeds, apply [[k']] to it; *)
(* otherwise propagate the error. I know of no standard *)
(* way to write this operator, [Haskell uses [[flip *)
(* fmap]].] , so I've chosen [[>>=+]], which you might *)
(* also choose to pronounce ``and then.''       *)

(* <error handling>=                            *)
infix 1 >>=+
fun e >>=+ k'  =  e >>= OK o k'
(* <boxed values 50>=                           *)
val _ = op >>=+ : 'a error * ('a -> 'b) -> 'b error
(* <error handling>=                            *)
fun errorList es =
  let fun cons (OK x, OK xs) = OK (x :: xs)
        | cons (ERROR m1, ERROR m2) = ERROR (m1 ^ "; " ^ m2)
        | cons (ERROR m, OK _) = ERROR m
        | cons (OK _, ERROR m) = ERROR m
  in  foldr cons (OK []) es
  end
(* <parsing combinators>=                       *)
type ('a, 'b) xformer = 
  'a stream -> ('b error * 'a stream) option
(* Sometimes a whole list of results are checked for *)
(* errors independently and then must be combined. *)
(* I call the combining operation [[errorList]]. [ *)
(* Haskell calls it [[sequence]].] I implement it by *)
(* folding over the list of possibly erroneous results, *)
(* combining all error messages.                *)
(* <boxed values 51>=                           *)
val _ = op errorList : 'a error list -> 'a list error
(* Stream transformers, which act as parsers    *)
(*                                              *)
(* Our ultimate goal is to turn streams of input lines *)
(* into streams of definitions. Along the way we may *)
(* also have streams of characters, ``tokens,'' types, *)
(* expressions, and more. To handle all these different *)
(* kinds of streams using a single set of operators, *)
(* I define a type representing a stream transformer. *)
(* A stream transformer from A to B takes a stream of A *)
(* 's as input and either succeeds, fails, or detects an *)
(* error:                                       *)
(*                                              *)
(*   * If it succeeds, it consumes zero or more A's from *)
(*  the input stream and produces exactly one B. *)
(*  It returns a pair containing [[OK]] B plus  *)
(*  whatever A's were not consumed.             *)
(*   * If it fails, it returns [[NONE]].        *)
(*   * If it detects an error, it returns a pair *)
(*  containing [[ERROR]] m, where m is a message, *)
(*  plus whatever A's were not consumed.        *)
(*                                              *)
(* <boxed values 51>=                           *)
type ('a, 'b) xformer = ('a, 'b) xformer
(* If we apply [[streamOfUnfold]] to an [[('a, 'b) *)
(* xformer]], we get a function that maps a stream of A *)
(* 's to a stream of B's-with-error.            *)

(* <parsing combinators>=                       *)
fun pure y = fn xs => SOME (OK y, xs)
(* Error-free transformers and their composition *)
(*                                              *)
(* The [[pure]] combinator takes a B as argument and *)
(* returns an \atob transformer that consumes no A's as *)
(* input and produces the given B:              *)
(* <boxed values 52>=                           *)
val _ = op pure : 'b -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
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
(* For the combination [[tx_f <*> tx_b]] to succeed, *)
(* both [[tx_f]] and [[tx_b]] must succeed. So I use *)
(* nested case analysis.                        *)
(* <boxed values 53>=                           *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* has a special operator [[<>]], which is also *)
(* pronounced ``applied to.'' It combines a B-to-C *)
(* function with an \atob transformer to produce an \ *)
(* atoc transformer.                            *)
(* <boxed values 54>=                           *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* <boxed values 55>=                           *)
val _ = op fst    : ('a * 'b) -> 'a
val _ = op snd    : ('a * 'b) -> 'b
val _ = op pair   : 'a -> 'b -> 'a * 'b
val _ = op curry  : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
val _ = op curry3 : ('a * 'b * 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)
(* <parsing combinators>=                       *)
infix 1 <|>
fun t1 <|> t2 = (fn xs => case t1 xs of SOME y => SOME y | NONE => t2 xs) 
(* The combinator [[<*>]] creates parsers that read *)
(* things in sequence; but it can't make a choice. *)
(* If any parser in the sequence fails, the whole *)
(* sequence fails. To make a choice, as in ``[[val]] or *)
(* expression or [[define]] or [[use]],'' we use a *)
(* choice operator. The choice operator is written *)
(* [[<|>]] and pronounced ``or.'' If [[t1]] and [[t2]] *)
(* are both \atob transformers, then [[t1 <|> t2]] is an *)
(* \atob transformer that first tries [[t1]], then tries *)
(* [[t2]], succeeding if either succeeds, detecting an *)
(* error if either detects an error, and failing only if *)
(* both fail. To assure that the result has a   *)
(* predictable type no matter which transformer is used, *)
(* both [[t1]] and [[t2]] have to have the same type. *)
(* <boxed values 56>=                           *)
val _ = op <|> : ('a, 'b) xformer * ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
infix 3 <* *>
fun p1 <*  p2 = curry fst <$> p1 <*> p2
fun p1  *> p2 = curry snd <$> p1 <*> p2

infixr 4 <$
fun v <$ p = (fn _ => v) <$> p
(* The abbreviations are formed by modifying the [[<*>]] *)
(* or [[<>]] operator to remove the angle bracket on the *)
(* side containing the result we don't care about. For *)
(* example,                                     *)
(*                                              *)
(*   * Parser [[p1 <* p2]] reads the input of [[p1]] and *)
(*  then the input of [[p2]], but it returns only the *)
(*  result of [[p1]].                           *)
(*   * Parser [[p1 *> p2]] reads the input of [[p1]] and *)
(*  then the input of [[p2]], but it returns only the *)
(*  result of [[p2]].                           *)
(*   * Parser [[v < p]] parses the input the way [[p]] *)
(*   does, but it then ignores [[p]]'s result and *)
(*  instead produces the value [[v]].           *)
(*                                              *)
(* <boxed values 57>=                           *)
val _ = op <*  : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'b) xformer
val _ = op  *> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
val _ = op <$  : 'b               * ('a, 'c) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun one xs = case streamGet xs
               of NONE => NONE
                | SOME (x, xs) => SOME (OK x, xs)
(* The simplest input-inspecting parser is [[one]]. It's *)
(* an \atoa transformer that succeeds if and only if *)
(* there is a value in the input. If there's no value *)
(* input, [[one]] fails; it never signals an error. *)
(* <boxed values 58>=                           *)
val _ = op one : ('a, 'a) xformer
(* <parsing combinators>=                       *)
fun eos xs = case streamGet xs
               of NONE => SOME (OK (), EOS)
                | SOME _ => NONE
(* The counterpart of [[one]] is a parser that succeeds *)
(* if and only if there is no input?that is, if we have *)
(* reached the end of the stream. This parser, which is *)
(* called [[eos]], can produce no useful result, so it *)
(* produces the empty tuple, which has type [[unit]]. *)
(* <boxed values 59>=                           *)
val _ = op eos : ('a, unit) xformer
(* <parsing combinators>=                       *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* It can also be useful to peek at the contents of a *)
(* stream, without looking at any input, and while *)
(* ignoring errors.                             *)
(* <boxed values 60>=                           *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* <parsing combinators>=                       *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* And we might want to transform some input, then *)
(* rewind it back to the starting point. (Actions can't *)
(* be undone, but at least the input can be read again.) *)
(* <boxed values 61>=                           *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* <boxed values 62>=                           *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun oneEq x = sat (fn x' => x = x') one
(* <boxed values 63>=                           *)
val _ = op oneEq : ''a -> (''a, ''a) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>?
fun f <$>? tx =
  fn xs => case tx xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK y, xs) =>
                  case f y
                    of NONE => NONE
                     | SOME z => SOME (OK z, xs)
(* A more subtle condition is that a partial function *)
(* can turn an input into something we're looking for. *)
(* If we have an \atob transformer, and we compose it *)
(* with a function that given a B, sometimes produces a  *)
(* C, then we get an \atoxC transformer. Because there's *)
(* a close analogy with the application operator [[<>]], *)
(* I'm notating this partial application operator as [[< *)
(* >?]], with a question mark.                  *)
(* <boxed values 64>=                           *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* <boxed values 65>=                           *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* <boxed values 66>=                           *)
val _ = op notFollowedBy : ('a, 'b) xformer -> ('a, unit) xformer
(* <parsing combinators>=                       *)
fun many t = 
  curry (op ::) <$> t <*> (fn xs => many t xs) <|> pure []
(* Parsers for sequences                        *)
(*                                              *)
(* Inputs are full of sequences. A function takes a *)
(* sequence of arguments, a program is a sequence of *)
(* definitions, and a method definition contains a *)
(* sequence of expressions. To create transformers that *)
(* process sequences, we define function [[many]] and *)
(* [[many1]]. If [[t]] is an \atob transformer, then *)
(* [[many t]] is an \atoxlist-of-B transformer. It runs *)
(* [[t]] as many times as possible. And even if [[t]] *)
(* fails, [[many t]] always succeeds: when [[t]] fails, *)
(* [[many t]] returns an empty list of B's.     *)
(* <boxed values 67>=                           *)
val _ = op many  : ('a, 'b) xformer -> ('a, 'b list) xformer
(* I'd really like to write that first alternative as *)
(*                                              *)
(*  [[curry (op ::) <> t <*> many t]]           *)
(*                                              *)
(* but that formulation leads to instant death by *)
(* infinite recursion. If you write your own parsers, *)
(* it's a problem to watch out for.             *)

(* <parsing combinators>=                       *)
fun many1 t = 
  curry (op ::) <$> t <*> many t
(* Sometimes an empty list isn't acceptable. In that *)
(* case, use [[many1 t]], which succeeds only if [[t]] *)
(* succeeds at least once.                      *)
(* <boxed values 68>=                           *)
val _ = op many1 : ('a, 'b) xformer -> ('a, 'b list) xformer
(* Although [[many t]] always succeeds, [[many1 t]] can *)
(* fail.                                        *)

(* <parsing combinators>=                       *)
fun optional t = 
  SOME <$> t <|> pure NONE
(* Sometimes instead of zero, one, or many B's, we just *)
(* one zero or one; such a B might be called    *)
(* ``optional.'' For example, a numeric literal begins *)
(* with an optional minus sign. Function [[optional]] *)
(* turns an \atob transformer into an \atoxoptional-B *)
(* transformer. Like [[many t]], [[optional t]] always *)
(* succeeds.                                    *)
(* <boxed values 69>=                           *)
val _ = op optional : ('a, 'b) xformer -> ('a, 'b option) xformer
(* <parsing combinators>=                       *)
infix 2 <*>!
fun tx_ef <*>! tx_x =
  fn xs => case (tx_ef <*> tx_x) xs
             of NONE => NONE
              | SOME (OK (OK y),      xs) => SOME (OK y,      xs)
              | SOME (OK (ERROR msg), xs) => SOME (ERROR msg, xs)
              | SOME (ERROR msg,      xs) => SOME (ERROR msg, xs)
infixr 4 <$>!
fun ef <$>! tx_x = pure ef <*>! tx_x
(* Transformers made with [[many]] and [[optional]] *)
(* succeed even when there is no input. They also *)
(* succeed when there is input that they don't  *)
(* recognize.                                   *)
(*                                              *)
(* Error-detecting transformers and their composition *)
(*                                              *)
(* Sometimes an error is detected not by a parser but by *)
(* a function that is applied to the results of parsing. *)
(* A classic example is a function definition: if the *)
(* formal parameters are syntactically correct but *)
(* contain duplicate name, an error should be signalled. *)
(* We would transform the input into a value of type *)
(* [[name list error]]. But the transformer type already *)
(* includes the possibility of error, and we would *)
(* prefer that errors detected by functions be on the *)
(* same footing as errors detected by parsers, and that *)
(* they be handled by the same mechanisms. To enable *)
(* such handling, I define [[<*>!]] and [[<>!]] *)
(* combinator that merge function-detected errors with *)
(* parser-detected errors.                      *)
(* <boxed values 70>=                           *)
val _ = op <*>! : ('a, 'b -> 'c error) xformer * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
val _ = op <$>! : ('b -> 'c error)             * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
(* <support for lexical analysis>=              *)
type 'a lexer = (char, 'a) xformer
(* Lexical analyzers: transformers of characters *)
(*                                              *)
(* The interpreters in this book consume one line at a *)
(* time. But characters within a line may be split into *)
(* multiple tokens. For example, the line       *)
(*                                              *)
(*   (define list1 (x) (cons x '()))            *)
(*                                              *)
(* should be split into the tokens              *)
(*                                              *)
(*                                              *)
(*  (                                           *)
(*  define                                      *)
(*  list1                                       *)
(*  (                                           *)
(*  x                                           *)
(*  )                                           *)
(*  (                                           *)
(*  cons                                        *)
(*  x                                           *)
(*  '                                           *)
(*  (                                           *)
(*  )                                           *)
(*  )                                           *)
(*  )                                           *)
(*                                              *)
(* This section reusable transformers that are  *)
(* specialized to transform streams of characters into *)
(* something else, usually tokens.              *)
(* <boxed values 71>=                           *)
type 'a lexer = 'a lexer
(* The type [['a lexer]] should be pronounced ``lexer *)
(* returning [['a]].''                          *)

(* <support for lexical analysis>=              *)
fun isDelim c = Char.isSpace c orelse Char.contains "();" c
(* In popular languages, a character like a semicolon or *)
(* comma usually does not join with other tokens to form *)
(* a character. In this book, the left and right *)
(* parentheses keep to themselves and don't group with *)
(* other characters. And in just about every    *)
(* non-esoteric language, blank space separates tokens. *)
(* A character whose presence marks the end of one token *)
(* (and possibly the beginning of the next) is called a *)
(* delimiter. In this book, whitespace and parentheses *)
(* are the main delimiter characters. The semicolon, *)
(* which introduces a comment, also acts as a delimiter. *)
(* <boxed values 72>=                           *)
val _ = op isDelim : char -> bool
(* [[Char.isSpace]] recognizes all whitespace   *)
(* characters. [[Char.contains]] takes a string and a *)
(* character and says if the string contains the *)
(* character. These functions are in the initial basis *)
(* of Standard ML.                              *)

(* <support for lexical analysis>=              *)
val whitespace = many (sat Char.isSpace one)
(* All languages in this book ignore whitespace. Lexer *)
(* [[whitespace]] is typically combined with another *)
(* lexer using the [[*>]] operator.             *)
(* <boxed values 73>=                           *)
val _ = op whitespace : char list lexer
(* <support for lexical analysis>=              *)
fun intChars isDelim = 
  (curry (op ::) <$> oneEq #"-" <|> pure id) <*> many1 (sat Char.isDigit one) <*
                                                                                
  notFollowedBy (sat (not o isDelim) one)
(* The rules for integer literals are as follows: *)
(*                                              *)
(*   * The integer literal may begin with a minus sign. *)
(*   * It continues with one or more digits.    *)
(*   * If it is followed by character, that character *)
(*  must be a delimiter. (In other words, it must not *)
(*  be followed by a non-delimiter.)            *)
(*   * When the sequence of digits is converted to an *)
(*  [[int]], the arithmetic used in the conversion *)
(*  must not overflow.                          *)
(*                                              *)
(* Function [[intChars]] does the lexical analysis to *)
(* grab the characters; [[intFromChars]] handles the *)
(* conversion and its potential overflow, and   *)
(* [[intToken]] puts everything together. Because not *)
(* every language has the same delimiters, both *)
(* [[intChars]] and [[intToken]] receive a predicate *)
(* that identifies delimiters.                  *)
(* <boxed values 74>=                           *)
val _ = op intChars     : (char -> bool) -> char list lexer
(* <support for lexical analysis>=              *)
fun intFromChars (#"-" :: cs) = 
      intFromChars cs >>=+ ~
  | intFromChars cs =
      (OK o valOf o Int.fromString o implode) cs
      handle Overflow => ERROR
                        "this interpreter can't read arbitrarily large integers"
(* Function [[intFromChars]] works by combining three *)
(* functions from Standard ML's initial basis. Function *)
(* [[implode]] converts to string; [[Int.fromString]] *)
(* converts to [[int option]] (raising [[Overflow]] if *)
(* the literal is too big); and [[valOf]] converts from *)
(* [[int option]] to [[int]]. The [[ ]] function, which *)
(* is used when we see a minus sign, is ML's way of *)
(* writing negation.                            *)
(* <boxed values 75>=                           *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* <boxed values 76>=                           *)
val _ = op intToken : (char -> bool) -> int lexer
(* <support for parsing>=                       *)
(* token, isLiteral, and
   tokenString can be defined
   differently in each language *)
(* YOU CAN SEE EXAMPLE DEFINITIONS WHERE IN WHAT *)
(* APPENDIX, PLEASE?                            *)

(* <support for parsing>=                       *)
type srcloc = string * int
fun srclocString (source, line) =
  source ^ ", line " ^ Int.toString line
(* <support for parsing>=                       *)
fun errorAt msg loc =
  ERROR (msg ^ " in " ^ srclocString loc)
(* <support for parsing>=                       *)
type 'a located = srcloc * 'a
(* Parsers: reading tokens and source-code locations *)
(*                                              *)
(* [*] To read definitions, expressions, and types, *)
(* it helps to work at a higher level of abstraction *)
(* than individual characters. All the parsers in this *)
(* book use two stages: first a lexer groups characters *)
(* into tokens, then a parser transforms tokens into *)
(* syntax. Not all languages use the same tokens, so the *)
(* code in this section assumes that the type [[token]] *)
(* and two related functions are defined. Function *)
(* [[isLiteral]] tells us if a token was produced from *)
(* the given literal string; it is used in parsing. *)
(* function [[tokenString]] returns a string    *)
(* representation of any given token; it is used in *)
(* debugging.                                   *)
(* <boxed values 77>=                           *)
type token = token
val _ = op isLiteral : string -> token -> bool
val _ = op tokenString : token -> string
(* Source-code locations                        *)
(*                                              *)
(* To be able to say where things go wrong, we need to *)
(* track source-code locations. Compilers that take *)
(* themselves seriously, which includes all the *)
(* compilers I have built and most of the ones I have *)
(* worked on, report source-code locations right down to *)
(* the individual character: file broken.c, line 12, *)
(* column 17. In production compilers, such precision is *)
(* admirable. But in a pedagogical interpreter, the *)
(* desire for precision has to be balanced against the *)
(* need for simplicity. The best compromise is to track *)
(* only source file and line number. That's good enough *)
(* to help programmers find errors, and it eliminates *)
(* the bookkeeping that would otherwise be needed to *)
(* track column numbers.                        *)
(* <boxed values 77>=                           *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To signal an error at a given location, call *)
(* [[errorAt]].                                 *)
(* <boxed values 77>=                           *)
val _ = op errorAt : string -> srcloc -> 'a error
(* We can pair source-code locations with individual *)
(* lines and tokens. To make it easier to read the *)
(* types, I define a type abbreviation which says that a *)
(* value paired with a location is ``located.'' *)
(* <boxed values 77>=                           *)
type 'a located = 'a located
(* <support for parsing>=                       *)
fun locatedStream (streamname, inputs) =
  let val locations = streamZip (streamRepeat streamname,
                                 streamOfUnfold (fn n => SOME (n, n+1)) 1)
  in  streamZip (locations, inputs)
  end
(* All locations originate in a located stream of lines. *)
(* The locations share a filename, and the line numbers *)
(* are 1, 2, 3, ... and so on.                  *)
(* <boxed values 78>=                           *)
val _ = op locatedStream : string * line stream -> line located stream
(* <support for parsing>=                       *)
datatype 'a inline
  = EOL of int (* number of the line that ends here *)
  | INLINE of 'a

fun drainLine EOS = EOS
  | drainLine (SUSPENDED s)     = drainLine (force s)
  | drainLine (EOL _    ::: xs) = xs
  | drainLine (INLINE _ ::: xs) = drainLine xs
(* <parsing utilities>=                         *)
type 'a parser = (token located inline, 'a) xformer
(* <parsing utilities>=                         *)
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
(* Flushing bad tokens                          *)
(*                                              *)
(* A standard parser for a batch compiler needs only to *)
(* see a stream of tokens and to know from what *)
(* source-code location each token came. A batch *)
(* compiler can simply read all its input and report all *)
(* the errors it wants to report. [Batch compilers vary *)
(* widely in the ambitions of their parsers. Some simple *)
(* parsers report just one error and stop. Some *)
(* sophisticated parsers analyze the entire input and *)
(* report the smallest number of changes needed to make *)
(* the input syntactically correct. And some    *)
(* ill-mannered parsers become confused after an error *)
(* and start spraying meaningless error messages. But *)
(* all of them have access to the entire input. *)
(* We~don't. ] But an interactive interpreter may not *)
(* use an error as an excuse to read an indefinite *)
(* amount of input. It must instead bring its error *)
(* processing to a prompt conclusion and ready itself to *)
(* read the next line. To do so, it needs to know where *)
(* the line boundaries are! For example, if I find an *)
(* error on line 6, I want to read all the tokens on *)
(* line 6, throw them away, and start over again on *)
(* line 7. The nasty bit is that I want to do it without *)
(* reading line 7?reading line 7 will take an action and *)
(* will likely have the side effect of printing a *)
(* prompt. And I want it to be the correct prompt. *)
(* I therefore define a new type constructor [[inline]]. *)
(* A value of type [['a inline]] either contains an *)
(* value of type [['a]] that occurs in a line, or and *)
(* end-of-line marker. A stream of such values can be *)
(* drained up to the end of the line. [At~some future *)
(* point I~may need to change [[drainLine]] to keep the *)
(* [[EOL]] in order to track locations in \uprolog. ] *)
(* <boxed values 79>=                           *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <boxed values 79>=                           *)
type 'a parser = 'a parser
(* The [[EOL]] and [[INLINE]] constructors are essential *)
(* for error recovery, but for parsing, they just get in *)
(* the way. Our first order of business is to define *)
(* analogs of [[one]] and [[eos]] that ignore [[EOL]]. *)
(* Parser [[token]] takes one token; parser [[srcloc]] *)
(* takes one source-code location; and parser   *)
(* [[noTokens]] succeeds only if there are no tokens *)
(* left in the input. They are built on top of  *)
(* ``utility'' parsers [[eol]] and [[inline]]. The two *)
(* utility parsers have different contracts; [[eol]] *)
(* succeeds only when at [[EOL]], but [[inline]] scans *)
(* past [[EOL]] to look for [[INLINE]].         *)
(* <boxed values 79>=                           *)
val _ = op eol      : ('a inline, int) xformer
val _ = op inline   : ('a inline, 'a)  xformer
val _ = op token    : token parser
val _ = op srcloc   : srcloc parser
val _ = op noTokens : unit parser
(* <parsing utilities>=                         *)
fun @@ p = pair <$> srcloc <*> p
(* Sometimes the easiest way to keep track of   *)
(* source-code locations is to pair a source-code *)
(* location with a result from a parser. This happens *)
(* just often enough that I find it worth while to *)
(* define the [[@@]] function. (Associate the word *)
(* ``at'' with the idea of ``location.'') The code uses *)
(* a dirty trick: it works because [[srcloc]] looks at *)
(* the input but does not consume any tokens.   *)
(* <boxed values 80>=                           *)
val _ = op @@ : 'a parser -> 'a located parser
(* <parsing utilities>=                         *)

infix 0 <?>
fun p <?> expected = p <|> errorAt ("expected " ^ expected) <$>! srcloc
(* Parsers that report errors                   *)
(*                                              *)
(* The [[<?>]] operator typically follows a list of *)
(* alternatives, as in the parser for definitions on *)
(* page [->]. It reports that it couldn't recognize its *)
(* input, and it gives the source-code location of the *)
(* unrecognized token. If there is no token, there is no *)
(* error?at end of file, rather than signal an error, a *)
(* parser made using [[<?>]] fails.             *)
(* <boxed values 81>=                           *)
val _ = op <?> : 'a parser * string -> 'a parser
(* <parsing utilities>=                         *)
infix 4 <!>
fun p <!> msg =
  fn tokens => (case p tokens
                  of SOME (OK _, unused) =>
                       (case peek srcloc tokens
                          of SOME loc => SOME (errorAt msg loc, unused)
                           | NONE => NONE)
                   | _ => NONE)
(* <parsing utilities>=                         *)
fun literal s =
  ignore <$> sat (isLiteral s) token
(* Another common error-detecting technique is to use a *)
(* parser [[p]] to detect some input that shouldn't be *)
(* there. We can't simply combine [[p]] with [[errorAt]] *)
(* and [[srcloc]] in the same way that [[<?>]] does, *)
(* because we have two goals: consume the tokens *)
(* recognized by [[p]], and also report the error at the *)
(* location of the first of those tokens. We can't use *)
(* [[errorAt]] until after [[p]] succeeds, but we have *)
(* to use [[srcloc]] on the input stream as it is before *)
(* [[p]] is run. My solution is to define a special *)
(* combinator that keeps a copy of the tokens inspected *)
(* by [[p]]. If parser [[p]] succeeds, then parser [[p *)
(* <!> msg]] consumes the tokens consumed by [[p]] and *)
(* reports error [[msg]] at the location of [[p]]'s *)
(* first token.                                 *)
(* <boxed values 82>=                           *)
val _ = op <!> : 'a parser * string -> 'b parser
(* Keywords, brackets, and other literals       *)
(*                                              *)
(* It's extremely common to want to recognize literal *)
(* tokens, like the keyword [[if]] or a left or right *)
(* parenthesis. The [[literal]] parser accepts any token *)
(* whose concrete syntax is an exact match for the given *)
(* string argument.                             *)
(* <boxed values 82>=                           *)
val _ = op literal : string -> unit parser
(* Like the type [[token]], the function [[isLiteral]] *)
(* is different for each programming language in this *)
(* book.                                        *)

(* <parsing utilities>=                         *)
infix  6 --<
infixr 7 >-- 
    (* if we want to mix these operators, they can't have equal precedence *)
fun (a >-- p) = literal a *> p
fun (p --< a) = p <* literal a
(* When it succeeds, the [[literal]] parser returns the *)
(* empty tuple, which is not useful for anything. This *)
(* empty tuple can be ignored by writing parsers like *)
(* [[literal "(" *> p]], but notationally, this is a *)
(* towering nuisance. Instead, I define new combinators *)
(* [[?<]] and [[>?]] so I can write parsers like [["(" > *)
(* ? p]]. Theses combinators have higher precedence than *)
(* [[<*>]], so they ``pull in'' literal strings that *)
(* appear in sequences. As a mnemonic, the angle bracket *)
(* ``swallows'' the literal we want to ignore (or if you *)
(* prefer, it points to what we keep).          *)
(* <boxed values 83>=                           *)
val _ = op >-- : string    * 'a parser -> 'a parser
val _ = op --< : 'a parser * string    -> 'a parser
(* <parsing utilities>=                         *)

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
(* Bracketed expressions                        *)
(*                                              *)
(* Almost every language in this book uses      *)
(* parenthesis-prefix syntax (Scheme syntax). The *)
(* [[bracket]] [I~have spent entirely too much time *)
(* working with Englishmen who call parentheses *)
(* ``brackets.'' I~now find it hard even to \emph{say} *)
(* the word ``parenthesis,'' let alone put them in *)
(* my~code. So~the function is called [[bracket]]. ] *)
(* function creates a parser that recognizes inputs of *)
(* the form                                     *)
(*                                              *)
(*  ( keyword stuff )                           *)
(*                                              *)
(* The [[bracket]] function embodies some useful error *)
(* handling:                                    *)
(*                                              *)
(*   * It takes an extra parameter [[expected]], which *)
(*  says, when anything goes wrong, what the parser *)
(*  was expecting in the way of stuff.          *)
(*   * If something does go wrong parsing stuff, *)
(*  it calls [[scanToCloseParen]] to scan past all *)
(*  the tokens where stuff was expected, up to and *)
(*  including the matching close parenthesis.   *)
(*                                              *)
(* Once the parser sees the opening parenthesis and the *)
(* keyword, it is committed: either parser [[p]] parses *)
(* stuff correctly, or there's an error. [*]    *)
(* <boxed values 84>=                           *)
val _ = op bracket          : string -> string -> 'a parser -> 'a parser
val _ = op scanToCloseParen : srcloc parser
(* <parsing utilities>=                         *)
fun nodups (what, where') (loc, names) =
  let fun dup [] = OK names
        | dup (x::xs) = if List.exists (fn y : string => y = x) xs then
                          errorAt (what ^ " " ^ x ^ " appears twice in " ^
                                                                     where') loc
                        else
                          dup xs
  in  dup names
  end
(* Detection of duplicate names                 *)
(*                                              *)
(* Most of the languages in this book allow you to *)
(* define functions or methods that take formal *)
(* parameters. It is never permissible to use the same *)
(* name for formal parameters in two different  *)
(* positions. There are surprisingly many other places *)
(* where it's not acceptable to have duplicate in a list *)
(* of strings. Function [[nodups]] takes two Curried *)
(* arguments: a pair saying what kind of thing might be *)
(* duplicated and where it appeared, followed by a pair *)
(* containing a list of names and the source-code *)
(* location of the list. If there are no duplicates, it *)
(* returns the list of names; otherwise it raises the *)
(* [[SyntaxError]] exception.                   *)
(* <boxed values 85>=                           *)
val _ = op nodups : string * string -> srcloc * name list -> name list error
(* Function [[List.exists]] is like the micro-Scheme *)
(* [[exists?]]. It is in the initial basis for  *)
(* Standard ML.                                 *)

(* <code used to debug parsers>=                *)
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
(* Code used to debug parsers                   *)
(*                                              *)
(* When debugging parsers, I often find it helpful to *)
(* dump out the tokens that a parser is looking at. *)
(* I want to dump all the tokens that are available *)
(* without triggering the action of reading another line *)
(* of input. I believe it's safe to read until I have *)
(* got to both an end-of-line marker and an unforced *)
(* suspension.                                  *)
(* <boxed values 86>=                           *)
val _ = op safeTokens : token located inline stream -> token list
(* <code used to debug parsers>=                *)
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
(* The [[wrap]] function can be used to wrap a parser; *)
(* it shows what the parser was looking for, what tokens *)
(* it was looking at, and whether it found something. *)
(* <boxed values 87>=                           *)
val _ = op wrap : string -> 'a parser -> 'a parser
(* <an interactive reader>=                     *)
fun echoTagStream lines = 
  let fun echoIfTagged line =
        if (String.substring (line, 0, 2) = ";#" handle _ => false) then
          print line
        else
          ()
  in  postStream (lines, echoIfTagged)
  end
(* Testing support                              *)
(*                                              *)
(* Let's get the testing support out of the way first. *)
(* As in the C code, I want to print out any line read *)
(* that begins with the special string [[;#]]. This *)
(* string is a formal comment that helps me test the *)
(* chunks marked [[]]. In the ML code,          *)
(* I can do the job in a very modular way: I define a *)
(* post-stream action that prints any line meeting the *)
(* criterion. Function [[echoTagStream]] transforms a *)
(* stream of lines to a stream of lines, adding the *)
(* behavior I want.                             *)
(* <boxed values 88>=                           *)
val _ = op echoTagStream : line stream -> line stream 
(* <an interactive reader>=                     *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* Lexing and parsing with error handling       *)
(*                                              *)
(* The next step is error handling. When the code *)
(* detects an error it prints a message using function *)
(* [[errorln]].                                 *)
(* <boxed values 89>=                           *)
val _ = op errorln : string -> unit
(* <an interactive reader>=                     *)
fun stripErrors xs =
  let fun next xs =
        case streamGet xs
          of SOME (ERROR msg, xs) => (errorln ("error: " ^ msg); next xs)
           | SOME (OK x, xs) => SOME (x, xs)
           | NONE => NONE
  in  streamOfUnfold next xs
  end
(* The basic error handler strips and prints errors. *)
(* <boxed values 90>=                           *)
val _ = op stripErrors : 'a error stream -> 'a stream
(* <an interactive reader>=                     *)
fun lexLineWith lexer =
  stripErrors o streamOfUnfold lexer o streamOfList o explode
(* An error detected during lexical analysis is printed *)
(* without any information about source-code locations. *)
(* That's because, to keep things somewhat simple, *)
(* I've chosen to do lexical analysis on one line at a *)
(* time, and I don't keep track of the line's   *)
(* source-code location.                        *)
(* <boxed values 91>=                           *)
val _ = op lexLineWith : token lexer -> line -> token stream
(* <an interactive reader>=                     *)
fun parseWithErrors parser =
  let fun adjust (SOME (ERROR msg, tokens)) = SOME (ERROR msg, drainLine tokens)
        | adjust other = other
  in  streamOfUnfold (adjust o parser)
  end
(* When an error occurs during parsing, I drain the rest *)
(* of the tokens on the line where the error occurred. *)
(* I don't strip the errors at this point; errors need *)
(* to make it through to the reader because when an *)
(* error is detected, the prompt may need to be *)
(* adjusted.                                    *)
(* <boxed values 92>=                           *)
val _ = op parseWithErrors : 'a parser -> token located inline stream -> 'a
                                                                    error stream
(* <an interactive reader>=                     *)
type prompts   = { ps1 : string, ps2 : string }
val stdPrompts = { ps1 = "-> ", ps2 = "   " }
val noPrompts  = { ps1 = "", ps2 = "" }
(* Prompts                                      *)
(*                                              *)
(* START HERE! WE BUILD ON THE UNIX SHELL MODEL OF *)
(* HAVING TWO PROMPT STRINGS.                   *)
(*                                              *)
(* PS1 IS THE PROMPT THAT'S PRINTED WHEN THE INTERPRETER *)
(* IS WAITING FOR THE USER TO ENTER A DEFINITION. PS2 IS *)
(* THE PROMPT THAT'S PRINTED WHEN THE USER HITS A *)
(* NEWLINE BUT THE CURRENT DEFINITION IS NOT YET *)
(* COMPLETE. TO TURN OF PROMPTING ENTIRELY, SET THEM *)
(* BOTH TO THE EMPTY STRING.                    *)
(*                                              *)
(* <boxed values 93>=                           *)
type prompts = prompts
val _ = op stdPrompts : prompts
val _ = op noPrompts  : prompts
(* <an interactive reader>=                     *)
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
(* The other job of the [[reader]] function is to *)
(* deliver the right prompt in the right situation. *)
(* START EDITING HERE.                          *)
(*                                              *)
(* The prompt is initially [[ps1]]. It is set to [[ps2]] *)
(* every time a token is produced, then reset to [[ps1]] *)
(* every time we attempt to parse a definition. [*] *)
(* <boxed values 94>=                           *)
val _ = op reader : token lexer * 'a parser -> prompts -> string * line stream
                                                                    -> 'a stream
val _ = op lexAndDecorate : srcloc * line -> token located inline stream
  in  
      stripErrors (preStream (setPrompt ps1, edefs))
  end 
(* The abstractions are useful for reading all kinds of *)
(* input, not just computer programs, and I encourage *)
(* you to use them in your own projects. But here are *)
(* two words of caution: with so many abstractions in *)
(* the mix, the parsers are tricky to debug. And while *)
(* some parsers built from combinators are very *)
(* efficient, mine aren't.                      *)

(* <lexical analysis ((usm))>=                  *)
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
(* <boxed values 32>=                           *)
val _ = op smalltalkToken : token lexer
end
(* The [[isDelim]] on the right of [[val isDelim]] is *)
(* from [[]]. The [[val isDelim]]               *)
(* introduces a new [[isDelim]] that recognizes square *)
(* brackets as delimiters.                      *)



(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* Interpreter and operational semantics        *)
(*                                              *)
(* This section presents the abstract syntax,   *)
(* operational semantics, and implementation of *)
(* uSmalltalk.                                  *)
(*                                              *)
(* Abstract syntax and values                   *)
(*                                              *)
(* The abstract-syntax constructors [[VAR]], [[SET]], *)
(* [[SEND]], [[BEGIN]], and [[BLOCK]] resemble the kinds *)
(* of abstract syntax you have seen in other    *)
(* interpreters. Three other constructors solve problems *)
(* that are unique to Smalltalk.                *)
(*                                              *)
(*   * Literal values require special treatment. *)
(*  A literal value must ultimately stand for an *)
(*  object, and the object must have a class, but *)
(*  while the interpreter is being bootstrapped, the *)
(*  classes aren't yet defined (\secref         *)
(*  small.bootstrap). So for example, we can't create *)
(*  a complete representation of a literal integer *)
(*  until the class [[Integer]] is defined.     *)
(*                                              *)
(*  To solve this problem, we handle literals   *)
(*  somewhat differently than in other interpreters. *)
(*  The [[LITERAL]] node doesn't contain a complete *)
(*  value; it contains only a representation. Before *)
(*  the representation becomes a full-fledged value, *)
(*  it must be associated with a class.         *)
(*   * Once we do have a full-fledged value, we put it *)
(*  in a [[VALUE]] node, which includes both a class *)
(*  and a represention.                         *)
(*   * The [[SUPER]] node makes it easy to recognize *)
(*  messages to [[super]] and give them the proper *)
(*  semantics.                                  *)
(*                                              *)
(* <abstract syntax and values ((usm))>=        *)
datatype exp = VAR     of name
             | SET     of name * exp
             | SEND    of srcloc * name * exp * exp list
             | BEGIN   of exp list
             | BLOCK   of name list * exp list
             | LITERAL of rep
             | VALUE   of value
             | SUPER
(* Unlike other interpreters in this book, the  *)
(* uSmalltalk interpreter keeps track of source-code *)
(* locations. The [[srcloc]] field in the [[SEND]] node *)
(* is used in diagnostic error messages.        *)

(* In addition to our old friends [[VAL]], [[EXP]], and *)
(* [[USE]], a definition may be a block definition *)
(* ([[DEFINE]]) or a class definition ([[CLASSD]]). *)
(* <abstract syntax and values ((usm))>=        *)
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
(* In a compiled or bytecoded implementation of *)
(* Smalltalk, the representation of an object is a *)
(* sequence of machine words. The methods, and in *)
(* particular the primitive methods, ``know'' which *)
(* words stand for integers, which words are slots for *)
(* instance variables, and so on. But our interpreter is *)
(* written in ML, which doesn't provide direct access to *)
(* machine words. In our implementation, we define a *)
(* [[rep]] type for representations. The representation *)
(* of a user-defined object is an environment giving the *)
(* locations of instance variables. Representations of *)
(* arrays, numbers, symbols, blocks, and classes are *)
(* primitive.                                   *)
(* <abstract syntax and values ((usm))>=        *)
and    rep = USER     of value ref env (* collection of named instance variables
                                                                              *)
           | ARRAY    of value Array.array
           | NUM      of int
           | SYM      of name
           | CLOSURE  of name list * exp list * value ref env * class
           | CLASSREP of class
(* A [[CLOSURE]] is a representation of a block; it *)
(* captures not only the environment used to bind *)
(* variables, but also the class used to interpret *)
(* messages to [[super]].                       *)

(* The representation of a class includes its   *)
(* superclass, instance variables, methods.     *)
(* <abstract syntax and values ((usm))>=        *)
and class  = CLASS of { name    : name            (* name of the class *)
                      , super   : class option    (* superclass, if any *)
                      , ivars   : string list     (* instance variables *)
                      , methods : method env      (* both exported and private
                                                                              *)
                      , id      : int             (* uniquely identifies class
                                                                              *)
                      }
(* Except for the distinguished root class, [[Object]], *)
(* every class has a superclass. A class's [[ivars]] and *)
(* [[methods]] lists include only the instance variables *)
(* and methods defined in that class, not those of its *)
(* superclass.                                  *)

(* uSmalltalk has two kinds of methods. Primitive *)
(* methods are represented as ML functions; user-defined *)
(* methods are represented as abstract syntax, which *)
(* includes parameters, local variables, and a body. *)
(* In each user-defined method, we also store the *)
(* superclass of the class in which the method is *)
(* defined, which we use to interpret messages sent to *)
(* [[super]] from within that method.           *)
(* <abstract syntax and values ((usm))>=        *)
and method
  = PRIM_METHOD of name * (value * value list -> value)
  | USER_METHOD of { name : name, formals : name list, locals : name list, body
                                                                           : exp
                   , superclass : class (* used to send messages to super *)
                   }
(* Finally, a value is a combination of class and *)
(* representation. The representation is inherently *)
(* either a primitive representation or a collection of *)
(* instance variables, not a combination of both; it is *)
(* therefore not useful to inherit from a class with a *)
(* primitive representation.                    *)
(* <abstract syntax and values ((usm))>=        *)
withtype value = class * rep
(* As in the implementation of micro-Scheme, a primitive *)
(* method might raise the [[RuntimeError]] exception. *)
(* Because the uSmalltalk interpreter uses more mutable *)
(* state than other interpreters and is therefore harder *)
(* to get right, we also define the exception   *)
(* [[InternalError]], which indicates a bug in the *)
(* interpreter. Raising [[InternalError]] is the moral *)
(* equivalent of an assertion failure in a language *)
(* like C.                                      *)
(* <abstract syntax and values ((usm))>=        *)
exception RuntimeError  of string (* error caused by user *)
exception InternalError of string (* bug in the interpreter *)
(* <abstract syntax and values ((usm))>=        *)
fun className (CLASS {name, ...}) = name
fun classId   (CLASS {id,   ...}) = id
(* Creating the primitive classes and values    *)
(*                                              *)
(* Utilities for manipulating classes           *)
(*                                              *)
(* Because a class can point to its superclass, the type *)
(* [[class]] has to be a recursive type implemented as *)
(* an ML [[datatype]]. To get access to information *)
(* about a class, we have to write a pattern match. When *)
(* all we want is a class's name or its unique  *)
(* identifier, pattern matching is fairly heavy *)
(* notation, so we provide two convenience functions. *)
(* <boxed values 1>=                            *)
val _ = op className : class -> name
val _ = op classId   : class -> int
(* <abstract syntax and values ((usm))>=        *)
fun methodName (PRIM_METHOD (n, _)) = n
  | methodName (USER_METHOD { name, ... }) = name
fun renameMethod (n, PRIM_METHOD (_, f)) = PRIM_METHOD (n, f)
  | renameMethod _ = raise InternalError "renamed user method"
fun methods l = foldl (fn (m, rho) => bind (methodName m, m, rho)) emptyEnv l
(* We extract a name from a method using another *)
(* convenience function, [[methodName]]. Other  *)
(* manipulations of methods include [[renameMethod]], *)
(* which is used when a user class wants to use a *)
(* primitive method with a name other than the one we *)
(* built in, and [[methods]], which builds an   *)
(* environment suitable for use in a class.     *)
(* <boxed values 2>=                            *)
val _ = op methodName   : method -> name
val _ = op methods      : method list -> method env
val _ = op renameMethod : name * method -> method
(* <abstract syntax and values ((usm))>=        *)
local 
  val n = ref 10 (* new classes start here *)
  fun uid () = !n before n := !n + 1
in
  fun mkClass name super ivars ms =
    CLASS { name = name, super = SOME super, ivars = ivars, methods = methods ms
                                                                               ,
            id = uid () }
end
(* To build a class, we keep a private supply of unique *)
(* identifiers. Identifiers below 10 are reserved for *)
(* built-in classes not created with [[mkClass]]; the *)
(* current implementation uses only id 1, for   *)
(* [[Object]], and id 0, for a bootstrapping class. No *)
(* class ever has a negative identifier.        *)
(* <boxed values 3>=                            *)
val _ = op mkClass : name -> class -> name list -> method list -> class


(*****************************************************************)
(*                                                               *)
(*   BOOTSTRAPPING SUPPORT                                       *)
(*                                                               *)
(*****************************************************************)

(* <bootstrapping support>=                     *)
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
(* We break the circularity by defining a function *)
(* [[mkInteger]]. If called before the interpreter is *)
(* bootstrapped, [[mkInteger]] fails. If called *)
(* afterward, [[mkInteger]] creates a value of class *)
(* [[SmallInteger]]. We treat symbols and arrays in *)
(* similar fashion.                             *)
(* <boxed values 4>=                            *)
val _ = op mkInteger : int        -> value
val _ = op mkSymbol  : string     -> value
val _ = op mkArray   : value list -> value
(* [*]                                          *)

(* Function [[valOf]] and exception [[Option]] are part *)
(* of the initial basis of Standard ML.         *)
(*                                              *)
(* \penalty-800                                 *)
(*                                              *)

(* <bootstrapping support>=                     *)
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
(* Once the initial basis has been read, the    *)
(* initialization code calls [[closeLiteralsCycle]] to *)
(* assign the appropriate classes to the ref cells. The *)
(* environment containing the initial basis is passed as *)
(* the parameter [[xi]]. [Xi is the Greek letter xi, *)
(* pronounced ``ksee.'']                        *)
(* <boxed values 5>=                            *)
val _ = op findInitialClass : string * value ref env -> class
(* [*]                                          *)

(* <bootstrapping support>=                     *)
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
(* Booleans                                     *)
(*                                              *)
(* We use the same technique for Booleans, except *)
(* instead of saving classes, we save values.   *)
(* <boxed values 6>=                            *)
val _ = op mkBoolean : bool -> value
(* <bootstrapping support>=                     *)
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
(* Blocks                                       *)
(*                                              *)
(* We use the technique again for blocks. It is not *)
(* actually required for blocks, but by declaring *)
(* [[Block]] and [[Boolean]] together, we help clarify *)
(* the relationship between them, especially the *)
(* implementations of the [[whileTrue:]] and    *)
(* [[whileFalse:]] methods.                     *)
(* <boxed values 7>=                            *)
val _ = op mkBlock : name list * exp list * value ref env * class -> value


(*****************************************************************)
(*                                                               *)
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* Parsing                                      *)
(*                                              *)
(* <parsing ((usm))>=                           *)
val blockDups         = nodups ("formal parameter",  "block")
fun methodDups kind f = nodups ("formal parameter",   kind ^ " " ^ f)
fun localDups  kind f = nodups ("local variable",     kind ^ " " ^ f)
fun ivarDups c        = nodups ("instance variable", "class " ^ c)
(* Smalltalk has simple rules for computing the arity of *)
(* a message based on the message's name: if the name is *)
(* symbolic, the message is binary (one receiver, one *)
(* argument); if the name is alphanumeric, the number of *)
(* arguments is the number of colons. Unfortunately, in *)
(* uSmalltalk a name can mix alphanumerics and symbols. *)
(* To decide the issue, we use the first character of a *)
(* message's name.                              *)
(* <parsing ((usm))>=                           *)
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
(* <parsing ((usm))>=                           *)
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
(* If any uSmalltalk code tries to change any of the *)
(* predefined ``pseudovariables,'' the [[settable]] *)
(* parser causes an error.                      *)

(* The remaining parser functions are mostly    *)
(* straightforward. The [[sharp]] function may call *)
(* [[mkSymbol]], [[mkInteger]], or [[mkArray]], which *)
(* must not be called until after the initial basis is *)
(* read in.                                     *)
(* <parsing ((usm))>=                           *)
and sharp tokens = (
         mkSymbol  <$> name
    <|>  mkInteger <$> int
    <|>  mkArray   <$> ("(" >-- many sharp --< ")")
    <|>  literal "#" <!> "# within # is not legal" 
    <|>  literal "[" <!> "[ within # is not legal"
    <|>  literal "]" <!> "] within # is not legal"
    ) tokens
(* The parser for definitions recognizes [[method]] and *)
(* [[class-method]], because if a class definition has *)
(* an extra right parenthesis, a [[method]] or  *)
(* [[class-method]] keyword might show up at top level. *)
(* <parsing ((usm))>=                           *)

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
(* <parsing ((usm))>=                           *)
val smalltalkSyntax = (smalltalkToken, def)


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVE BASICS                                            *)
(*                                                               *)
(*****************************************************************)

(* <primitive basics>=                          *)
type primitive = value * value list -> value
fun arityError n (receiver, args) =
  raise RuntimeError ("primitive method expected " ^ Int.toString n ^
                      " arguments; got " ^ Int.toString (length args))
fun unaryPrim  f = (fn (a, [])  => f  a     | ra => arityError 0 ra)
fun binaryPrim f = (fn (a, [b]) => f (a, b) | ra => arityError 1 ra)
fun primMethod name f = PRIM_METHOD (name, f)
(* Primitives                                   *)
(*                                              *)
(* Utilities for creating primitives            *)
(*                                              *)
(* We create most primitives directly from functions *)
(* written in ML. Here we turn unary and binary *)
(* functions into primitives, then turn primitives into *)
(* methods.                                     *)
(* <boxed values 8>=                            *)
val _ = op unaryPrim  : (value         -> value) -> primitive
val _ = op binaryPrim : (value * value -> value) -> primitive
val _ = op primMethod : name -> primitive -> method
(* <primitive basics>=                          *)
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
(* A few primitives are more easily created as user *)
(* methods. For them, we define function [[userMethod]]. *)
(* The only dodgy bit is the [[superclass]] field of the *)
(* user method. Because this class is used only to *)
(* define the meaning of messages to [[super]], and *)
(* because none of our predefined user methods sends *)
(* messages to [[super]], we can get away with a bogus *)
(* class that understands no messages.          *)
(*                                              *)
(* Function [[exp]] is an auxiliary function used to *)
(* parse a string into abstract syntax.         *)
(* <boxed values 9>=                            *)
val _ = op internalExp : string -> exp


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVE METHODS FOR [[OBJECT]] AND [[UNDEFINEDOBJECT]]    *)
(*                                                               *)
(*****************************************************************)

(* <primitive methods for [[Object]] and [[UndefinedObject]]>= *)
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
(* Object primitives                            *)
(*                                              *)
(* Equality                                     *)
(*                                              *)
(* Smalltalk defines equality as object identity: two *)
(* values are equal if and only if they are the same *)
(* object. Our primitive implementation compares *)
(* representations directly, using ML primitives. [*] *)
(* Here's how we justify the cases:             *)
(*                                              *)
(*   * ML equality on arrays is object identity. *)
(*   * Because numbers and symbols are immutable in both *)
(*  Smalltalk and ML, we can use ML equality on *)
(*  numbers and symbols, and it appears to the  *)
(*  uSmalltalk programmer that we are using object *)
(*  identity.                                   *)
(*   * The [[USER]] representation is an environment *)
(*  containing mutable reference cells. ML's [[ref]] *)
(*  function is also generative, so ML equality on *)
(*  ref cells is object identity. Comparing the *)
(*  representation of two [[USER]] objects compares *)
(*  their instance-variable environments, which are *)
(*  equal only if they contain the same ref cells, *)
(*  which is possible only if they represent the same *)
(*  uSmalltalk object.                          *)
(*   * Blocks, which are represented as closures, always *)
(*  compare unequal, even when compared with    *)
(*  themselves.                                 *)
(*   * Two classes are the same object if and only if *)
(*  they have the same unique identifier.       *)
(*                                              *)
(* <boxed values 10>=                           *)
val _ = op eqRep : value * value -> bool
(* \penalty-800                                 *)
(*                                              *)
(* Printing                                     *)
(*                                              *)
(* By default, an object prints as its class name in *)
(* angle brackets.                              *)
(* <primitive methods for [[Object]] and [[UndefinedObject]]>= *)
fun defaultPrint (self as (c, _)) = ( app print ["<", className c, ">"]; self )
(* Class membership                             *)
(*                                              *)
(* For [[memberOf]], the class [[c]] of [[self]] has to *)
(* be the same as the class [[c']] of the argument. For *)
(* [[kindOf]], it just has to be a subclass.    *)
(* <primitive methods for [[Object]] and [[UndefinedObject]]>= *)
fun memberOf ((c, _), (_, CLASSREP c')) = mkBoolean (classId c = classId c')
  | memberOf _ = raise RuntimeError "argument of isMemberOf: must be a class"

fun kindOf ((c, _), (_, CLASSREP (CLASS {id=u', ...}))) =
      let fun subclassOfClassU' (CLASS {super, id=u, ... }) =
            u = u' orelse (case super of NONE => false | SOME c =>
                                                            subclassOfClassU' c)
      in  mkBoolean (subclassOfClassU' c)
      end
  | kindOf _ = raise RuntimeError "argument of isKindOf: must be a class"
(* The [[error:]] primitive raises [[RuntimeError]]. *)
(* <primitive methods for [[Object]] and [[UndefinedObject]]>= *)
fun error (_, (_, SYM s)) = raise RuntimeError s
  | error (_, (c, _    )) =
      raise RuntimeError ("error: got class " ^ className c ^
                                                            "; expected Symbol")


(*****************************************************************)
(*                                                               *)
(*   BUILT-IN CLASSES [[OBJECT]] AND [[UNDEFINEDOBJECT]]         *)
(*                                                               *)
(*****************************************************************)

(* The distinguished root class [[Object]]      *)
(*                                              *)
(* Class [[Object]] is the ultimate superclass. By *)
(* putting [[self]] in its representation, we ensure *)
(* that every object has an instance variable called *)
(* [[self]]. We also make sure that every object *)
(* responds to messages in the [[Object]] protocol *)
(* described in Figure [->] on page [->].       *)
(* <built-in classes [[Object]] and [[UndefinedObject]]>= *)
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
(* The undefined object                         *)
(*                                              *)
(* Class [[UndefinedObject]], whose sole instance is  *)
(* [[nil]], redefines [[isNil]], [[notNil]], and *)
(* [[print]].                                   *)
(* <built-in classes [[Object]] and [[UndefinedObject]]>= *)
val nilClass = 
  mkClass "UndefinedObject" objectClass []
    [ primMethod "isNil"  (unaryPrim (fn _ => mkBoolean true))
    , primMethod "notNil" (unaryPrim (fn _ => mkBoolean false))
    , primMethod "print"  (unaryPrim (fn x => (print "nil"; x)))
    ]
(* To create the [[nil]] value, we have to bind *)
(* [[self]]; otherwise [[println]] won't work on *)
(* [[nil]].                                     *)
(* <built-in classes [[Object]] and [[UndefinedObject]]>= *)
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

(* Integer primitives                           *)
(*                                              *)
(* To print integers, we can't use ML's [[Int.toString]] *)
(* directly, because [[Int.toString]] renders a minus *)
(* sign as [[ ]]. We use [[String.map]] to convert [[ ]] *)
(*  to [[-]]. [*]                               *)
(* <primitive methods for remaining classes>=   *)
fun printInt (self as (_, NUM n)) =
      ( print (String.map (fn #"~" => #"-" | c => c) (Int.toString n))
      ; self
      )
  | printInt _ =
      raise RuntimeError ("cannot print when object inherits from Int")
(* <primitive methods for remaining classes>=   *)
fun binaryInt mk $ ((_, NUM n), (_, NUM m)) = mk ($ (n, m))
  | binaryInt _ _  ((_, NUM n), (c, _)) =
      raise RuntimeError ("numeric primitive expected numeric argument, got <"
                          ^ className c ^ ">")
  | binaryInt _ _  ((c, _), _) =
      raise RuntimeError ("numeric primitive method defined on <" ^ className c
                                                                          ^ ">")
fun arithop    $ = binaryPrim (binaryInt mkInteger $)
fun intcompare $ = binaryPrim (binaryInt mkBoolean $)
(* To create a new integer, you must pass an argument *)
(* that is represented by an integer.           *)
(* <primitive methods for remaining classes>=   *)
fun newInteger ((_, CLASSREP c), (_, NUM n)) = (c, NUM n)
  | newInteger _ = raise RuntimeError (
                                   "made new integer with non-int or non-class")
(* Symbol primitives                            *)
(*                                              *)
(* A symbol prints as its name, with no leading [[#]]. *)
(* <primitive methods for remaining classes>=   *)
fun printSymbol (self as (_, SYM s)) = (print s; self)
  | printSymbol _ = raise RuntimeError
                                 "cannot print when object inherits from Symbol"
(* To create a new symbol, you must pass an argument *)
(* that is represented by a symbol.             *)
(* <primitive methods for remaining classes>=   *)
fun newSymbol ((_, CLASSREP c), (_, SYM s)) = (c, SYM s)
  | newSymbol _ = raise RuntimeError (
                                 "made new symbol with non-symbol or non-class")
(* A new array contains all [[nil]]. [*] [*]    *)
(* <primitive methods for remaining classes>=   *)
fun newArray ((_, CLASSREP c), (_, NUM n)) = (c, ARRAY (Array.array (n, nilValue
                                                                             )))
  | newArray _ = raise RuntimeError
                                "Array new sent to non-class or got non-integer"
(* <primitive methods for remaining classes>=   *)
fun arrayPrimitive f ((_, ARRAY a), l) = f (a, l)
  | arrayPrimitive f _ = raise RuntimeError "Array primitive used on non-array"

fun arraySize (a, []) = mkInteger (Array.length a)
  | arraySize ra      = arityError 0 ra
(* When defining array primitives for [[at:]] and *)
(* [[at:put:]], we adjust for differing indexing *)
(* conventions: in Smalltalk, arrays are indexed from 1, *)
(* but in ML, arrays are indexed from 0.        *)
(* <primitive methods for remaining classes>=   *)
fun arrayAt (a, [(_, NUM n)]) = Array.sub (a, n - 1)  (* convert to 0-indexed *)
  | arrayAt (_, [_])  = raise RuntimeError "Non-integer used as array subscript"
  | arrayAt ra        = arityError 1 ra

fun arrayAtPut (a, [(_, NUM n), x]) = (Array.update (a, n-1, x); x)
  | arrayAtPut (_, [_, _]) = raise RuntimeError
                                           "Non-integer used as array subscript"
  | arrayAtPut ra          = arityError 2 ra
(* <primitive methods for remaining classes>=   *)
fun classPrimitive f = 
  unaryPrim (fn (meta, CLASSREP c) => f (meta, c)
              | _ => raise RuntimeError "class primitive sent to non-class")
(* A binary integer operation created with [[arith]] *)
(* expects as arguments two integers [[m]] and [[n]]; it *)
(* applies an operation [[]] to them and uses a creator *)
(* function [[mk]] to convert the result to a value. We *)
(* use [[binaryInt]] to build arithmetic and comparison. *)
(* <boxed values 11>=                           *)
val _ = op binaryInt  : ('a -> value) -> (int * int -> 'a)   -> value * value ->
                                                                           value
val _ = op arithop    :                  (int * int -> int)  -> primitive
val _ = op intcompare :                  (int * int -> bool) -> primitive
(* To create primitives that expect [[self]] to be an *)
(* array, we define [[arrayPrimitive]].         *)
(* <boxed values 11>=                           *)
val _ = op arrayPrimitive : (value array * value list -> value) -> primitive
(* Class primitives                             *)
(*                                              *)
(* The class primitives take both the metaclass and the *)
(* class as arguments.                          *)
(* <boxed values 11>=                           *)
val _ = op classPrimitive : (class * class -> value) -> primitive
(* <primitive methods for remaining classes>=   *)
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
(* Object creation                              *)
(*                                              *)
(* The most important primitive defined on classes is *)
(* [[new]]. To create a new object, we allocate fresh *)
(* instance variables, each containing [[nilValue]]. *)
(* Given the variables, we can allocate the object, and *)
(* finally we assign [[self]] to point to the object *)
(* itself.                                      *)
(* <boxed values 12>=                           *)
val _ = op mkIvars       : class -> value ref env
val _ = op newUserObject : class * class -> value
end
(* Showing protocols                            *)
(*                                              *)
(* The [[showProtocol]] function helps implement the *)
(* [[protocol]] and [[localProtocol]] primitives, which *)
(* are defined on class [[Class]]. Its implementation is *)
(* not very interesting. Function [[insert]] helps *)
(* implement an insertion sort, which we use to present *)
(* methods in alphabetical order.               *)
(* <primitive methods for remaining classes>=   *)
(* Function [[separate]] helps print a readable list of *)
(* formals for the error message. Function [[spaceSep]] *)
(* is a common special case.                    *)
(* <definition of [[separate]]>=                *)
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
(* The implementations of the primitives are easy; we *)
(* try to build a block containing the result, but if *)
(* the computation overflows, we answer the overflow *)
(* block instead.                               *)
(* <primitive methods for remaining classes>=   *)
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

(* Class [[Class]]                              *)
(*                                              *)
(* Class [[Class]] is in the interpreter so that *)
(* metaclasses can inherit from it. As explained in *)
(* Figure [->] on page [->], the methods that are *)
(* defined on class [[Class]], and therefore defined on *)
(* all class objects, are [[new]], [[protocol]], and *)
(* [[localProtocol]].                           *)
(* <remaining built-in classes>=                *)
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

(* Miscellaneous                                *)
(*                                              *)
(* We have a different version of [[use]] than in *)
(* micro-Scheme; [[echo]] is a Boolean, not a function. *)
(* <implementation of [[use]], with Boolean [[echo]]>= *)
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

(* <evaluation ((usm))>=                        *)
(* Support for tracing                          *)
(*                                              *)
(* Tracing support is divided into three parts: support *)
(* for printing indented messages, which is conditioned *)
(* on the value of the variable [[ --- trace]]; support *)
(* for maintaining a stack of source-code locations, *)
(* which is used to provide information when an error *)
(* occurs; and exposed tracing functions, which are used *)
(* in the main part of the interpreter. To keep the *)
(* details hidden from the rest of the interpreter, the *)
(* first two parts are made [[local]].          *)
(* <tracing ((usm))>=                           *)
local
  (* <private state and functions for printing indented traces ((usm))>= *)
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
  (* Here's the parser.                           *)
  (* <boxed values 33>=                           *)
  val _ = op name : string parser
  val _ = op int  : int    parser
  (* The [[traceMe]] function is used internally to decide *)
  (* whether to trace; it not only returns a Boolean but *)
  (* also decrements [[ --- trace]] if needed.    *)
  (* <boxed values 33>=                           *)
  val _ = op traceMe : value ref env -> bool
  (* The local variable [[tindent]] maintains the current *)
  (* trace state; [[indent]] uses it to print an  *)
  (* indentation string.                          *)
  (* <private state and functions for printing indented traces ((usm))>= *)
  val tindent = ref 0
  fun indent 0 = ()
    | indent n = (print "  "; indent (n-1))
  (* Any actual printing is done by [[tracePrint]], *)
  (* conditional on [[traceMe]] returning [[true]]. The *)
  (* argument [[direction]] of type [[indentation]] *)
  (* controls the adjustment of [[indent]]. For   *)
  (* consistency, we outdent from the previous level *)
  (* before printing a message; we indent from the current *)
  (* level after printing a message.              *)
  (* <private state and functions for printing indented traces ((usm))>= *)
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
  (* Printing of trace messages is conditional, but we *)
  (* always maintain a stack of source-code locations. The *)
  (* stack is displayed when an error occurs.     *)
  (* <private state and functions for mainting a stack of source-code locations
                                                                    ((usm))>= *)
  val locationStack = ref [] : (string * srcloc) list ref
  fun push srcloc = locationStack := srcloc :: !locationStack
  fun pop () = case !locationStack
                 of []     => raise InternalError "tracing stack underflows"
                  | h :: t => locationStack := t
in
  (* <exposed tracing functions ((usm))>=         *)
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
  (* Here are the tracing-related functions that are *)
  (* exposed to the rest of the interpreter. The  *)
  (* interpreter uses [[traceIndent]] to trace sends, *)
  (* [[outdentTrace]] to trace answers, and [[resetTrace]] *)
  (* to reset indentation.                        *)
  (* <boxed values 34>=                           *)
  val _ = op resetTrace     : unit -> unit
  val _ = op traceIndent    : string * srcloc -> value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op outdentTrace   :                    value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op showStackTrace : unit -> unit
end
(* To avoid confusion, tracing code typically avoids *)
(* [[print]] methods; instead, it uses [[valueString]] *)
(* to give information about a value.           *)
(* <tracing ((usm))>=                           *)
fun valueString (c, NUM n) = 
      String.map (fn #"~" => #"-" | c => c) (Int.toString n) ^
      valueString(c, USER [])
  | valueString (_, SYM v) = v
  | valueString (c, _) = "<" ^ className c ^ ">"
fun eval (e, rho, superclass, xi) =
  let (* <local helper functions of [[eval]]>=        *)
      fun findMethod (name, class) =
        let fun fm (CLASS { methods, super, ...}) =
              find (name, methods)
              handle NotFound m =>
                case super
                  of SOME c => fm c
                   | NONE   => raise RuntimeError
                                 (className class ^
                                            " does not understand message " ^ m)
      (* The first function, [[findMethod]], implements method *)
      (* search. If \sendToDispatchesm c imp, then calling \ *)
      (* monofindMethod (m, c) returns imp. Given m and c, if *)
      (* there is no imp such that \sendToDispatchesm c imp, *)
      (* then calling \monofindMethod (m, c) raises the *)
      (* exception NotFound m.                        *)
      (* <boxed values 14>=                           *)
      val _ = op findMethod : name * class -> method
      val _ = op fm         : class        -> method
      (* [*]                                          *)

        in  fm class
        end
      (* <local helper functions of [[eval]]>=        *)
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
      (* To evaluate a primitive method, we apply the method's *)
      (* function. To evaluate a user-defined method, we build *)
      (* a new environment. Function [[evalMethod]] implements *)
      (* the second part of the \rulenameSendUser rule: *)
      (* We compute rho' as [[rho']] using [[instanceVars]]. *)
      (* We compute rho'{x_1|->l_1, ..., x_n|->l_n} as  *)
      (* [[rho_x]] and rho'{x_1|->l_1, ..., x_n|->l_n, y_1 |-> *)
      (* l'_1, ..., y_k |->l'_k } as [[rho_y]]. The \ldotsnx *)
      (* are the list [[formals]], the \ldotsny are the list *)
      (* [[locals]], the \ldotsnv are the list [[actuals]], *)
      (* and e_m is [[body]].                         *)
      (* <boxed values 15>=                           *)
      val _ = op evalMethod   : method * value * value list -> value
      val _ = op instanceVars : value -> value ref env
      (* [*]                                          *)

      (* If [[receiver]] is a [[USER]] object, [[self]] is *)
      (* already part of its [[rep]]. For every other kind of *)
      (* object, [[instanceVars]] creates an environment that *)
      (* binds only [[self]].                         *)

      (* <local helper functions of [[eval]]>=        *)
      fun applyClosure ((formals, body, rho, superclass), actuals) =
        eval (BEGIN body, bindList (formals, map ref actuals, rho), superclass,
                                                                             xi)
        handle BindListLength => 
            raise RuntimeError ("Wrong number of arguments to block; expected "
                                                                               ^
                                "(value <block>" ^ spaceSep formals ^ ")")
      (* Function [[evalMethod]] handles every primitive *)
      (* method except [[value]]. To send the [[value]] *)
      (* message to a block, we need to make a recursive call *)
      (* to [[eval]]. Encapsulating a recursive call to *)
      (* [[eval]] in a [[PRIM_METHOD]] callable from  *)
      (* [[evalMethod]] would be difficult; it's much easier *)
      (* to build that ability into a helper function. *)
      (* <boxed values 16>=                           *)
      val _ = op applyClosure : (name list * exp list * value ref env * class) *
                                                             value list -> value
      (* <function [[ev]], the evaluator proper ((usm))>= *)
      fun ev (VALUE v) = v
      (* When we see a [[LITERAL]] node, we call [[mkInteger]] *)
      (* or [[mkSymbol]] to build the literal. It is unsafe to *)
      (* call these functions until we have read the initial *)
      (* basis and bootstrapped the interpreter; integer or *)
      (* symbol literals in the initial basis had better *)
      (* appear only inside method definitions. Evaluating *)
      (* such a literal calls [[mkInteger]] or [[mkSymbol]], *)
      (* and if you revisit chunks [->] and [->], you will see *)
      (* that it is safe to call [[mkInteger]] only after the *)
      (* interpreter is fully initialized.            *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (LITERAL c) = 
            (case c of NUM n => mkInteger n
                     | SYM n => mkSymbol n
                     | _ => raise InternalError "unexpected literal")
      (* The cases for [[VAR]] and [[SET]] are as we would *)
      (* expect, given that we have both local and global *)
      (* environments, just as in Impcore.            *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (VAR v) = !(find (v, rho) handle NotFound _ => find (v, xi))
        | ev (SET (n, e)) =
            let val v = ev e
                val cell = find (n, rho) handle NotFound _ => find (n, xi)
            in  cell := v; v
            end 
      (* [[                                           *)
      (* SUPER]], when used as an expression, acts just as *)
      (* [[self]] does.                               *)

      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (SUPER) = ev (VAR "self")
      (* Evaluation of [[BEGIN]] is as in micro-Scheme. *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, nilValue)
            end
      (* Evaluating a block means capturing the local *)
      (* environment and superclass in a closure.     *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (BLOCK (formals, body)) = mkBlock (formals, body, rho, superclass)
      (* First we evaluate the receiver and the arguments. *)
      (* Message send dispatches on the receiver, which is *)
      (* used to find the method that defines [[message]], *)
      (* except when the message is sent to [[super]], in *)
      (* which case we use the [[superclass]] of the currently *)
      (* running method. There is one case in which we do not *)
      (* use dynamic dispatch ([[findMethod]]); sending the *)
      (* [[value]] message to a block is built directly into *)
      (* the interpreter. Instead of calling [[findMethod]], *)
      (* we call the evaluator recursively through    *)
      (* [[applyClosure]]. This trick makes it impossible for *)
      (* a subclass of [[Block]] to redefine the [[value]] *)
      (* method?but there is nothing useful to inherit from *)
      (* [[Block]], so creating a subclass would be a *)
      (* pointless exercise. [*]                      *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (SEND (srcloc, message, receiver, args))  =
            let val obj as (class, rep) = ev receiver
                val args = map ev args
                val dispatchingClass = case receiver of SUPER => superclass | _
                                                                        => class
                (* We trace every send and answer only if the uSmalltalk *)
                (* variable [[ --- trace]] is set to a non-zero number. *)
                (* At every trace, we also decrement [[ --- trace]]. The *)
                (* code that builds the tracing output is protected by *)
                (* [[fn () => ]]...; it is executed only if tracing is *)
                (* turned on.                                   *)
                (* <definitions of message-tracing procedures>= *)
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
                (* Functions [[traceIndent]], [[outdentTrace]], and *)
                (* [[valueString]] are defined in [[<<tracing   *)
                (* ((usm))>>]]. Chunk [[]] also                 *)
                (* defines function [[showStackTrace]], which is called *)
                (* from chunk [->] to show the stack of active message *)
                (* sends after a run-time error.                *)

                fun performSend () =
                  case (message, rep)
                    of ("value", CLOSURE clo) => applyClosure (clo, args)
                     | _ => evalMethod (findMethod (message, dispatchingClass),
                                                                      obj, args)

            in  ( traceSend srcloc
                ; traceAnswer srcloc (performSend ())
                )
            end
      (* With these helper functions in place, we can write *)
      (* the evaluator. A [[VALUE]] node stands for itself. *)
      (* <boxed values 17>=                           *)
      val _ = op ev : exp -> value
      (* The implementation of message send is further *)
      (* complicated because we have built two trace  *)
      (* facilities into the interpreter: one traces every *)
      (* send and answer, and the other prints a stack trace *)
      (* in case of a run-time error. Both facilities are *)
      (* driven by [[traceSend]] and [[traceAnswer]], which *)
      (* are defined below.                           *)
      (*                                              *)
      (* \penalty-1000                                *)
      (*                                              *)

(* The evaluator therefore takes four arguments: an *)
(* expression to be evaluated; a local environment, *)
(* which binds instance variables, formal parameters, *)
(* and local variables; a class used to send message to  *)
(* [[super]]; and the global environment. These four *)
(* arguments correspond to the e, rho, \superclass, and  *)
(* xi used in the evaluation judgment \evale ==>\evalr *)
(* [']v. As usual, the states sigma and sigma' represent *)
(* states of the underlying ML interpreter, and they are *)
(* not passed explicitly.                       *)
(* <boxed values 13>=                           *)
val _ = op eval: exp * value ref env * class * value ref env -> value
val _ = op ev  : exp -> value
  in  ev e
  end
(* Because the rules for finding and evaluating methods *)
(* are relatively complex, we define several helper *)
(* functions that are private to [[eval]]. We then use *)
(* those functions to define [[ev]], which evaluates a *)
(* single expression in the context of the current *)
(* [[rho]], [[superclass]], and [[xi]].         *)

(* <evaluation ((usm))>=                        *)
(* To find a primitive method by name, we make the list *)
(* of primitive methods into an environment, then look *)
(* up the name in that environment.             *)
(* <definition of function [[primitiveMethod]]>= *)
val primitiveMethods = methods ((* <primitive methods [[::]]>=
                                                                              *)
                                primMethod "eqObject" (binaryPrim (mkBoolean o
                                                                      eqRep)) ::
                                (* <primitive methods [[::]]>=
                                                                              *)
                                primMethod "print" (unaryPrim defaultPrint) ::
                                (* Here are the primitive operations on small
                                                                   integers.  *)
                                (* [*]
                                                                              *)
                                (* <primitive methods [[::]]>=
                                                                              *)
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
                                (* In chunk [->], these primitive methods are
                                                                      used to *)
                                (* define class [[SmallInteger]].
                                                                              *)

                                (* <primitive methods [[::]]>=
                                                                              *)
                                primMethod "printSymbol" (unaryPrim  printSymbol
                                                                            ) ::
                                primMethod "newSymbol"   (binaryPrim newSymbol
                                                                            ) ::
                                (* Here are all the primitive array methods. [*]
                                                                              *)
                                (* <primitive methods [[::]]>=
                                                                              *)
                                primMethod "arrayNew:"    (binaryPrim
                                                                  newArray)   ::
                                primMethod "arraySize"    (arrayPrimitive
                                                                  arraySize)  ::
                                primMethod "arrayAt:"     (arrayPrimitive
                                                                  arrayAt)    ::
                                primMethod "arrayAt:Put:" (arrayPrimitive
                                                                  arrayAtPut) ::
                                (* In chunk [->], these primitive methods are
                                                                      used to *)
                                (* define class [[Array]].
                                                                              *)

                                (* Block primitives
                                                                              *)
                                (*
                                                                              *)
                                (* Actually, [[value]] is not a primitive; it is
                                                                        built *)
                                (* into [[eval]]. We create a primitive method
                                                                       called *)
                                (* [[value]] anyway, which we use in the
                                                                definition of *)
                                (* class [[Block]] (page [->]), so if there's a
                                                                       bug in *)
                                (* the interpreter, we get an informative error
                                                                     message. *)
                                (* <primitive methods [[::]]>=
                                                                              *)
                                primMethod "value" (fn _ => raise InternalError
                                              "hit primitive method 'value'") ::
                                (* <primitive methods [[::]]>=
                                                                              *)
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
(* Evaluating definitions; the read-eval-print loop *)
(*                                              *)
(* Most definitions are evaluated more or less as in *)
(* other interpreters, but class definitions require a *)
(* lot of special-purpose code, most of which is in the *)
(* function [[newClassObject]]. This function takes the *)
(* abstract syntax of a class definition and creates a *)
(* class object. [*] It also creates a metaclass, on *)
(* which it defines the class methods.          *)
(*                                              *)
(*   * Value [[class]] is the new class being declared, *)
(*  on which the instance methods are defined;  *)
(*  [[metaclass]] is the new metaclass, on which the *)
(*  class methods are defined.                  *)
(*   * Value [[super]] is the superclass from which the *)
(*  new class inherits; [[superMeta]] is its    *)
(*  metaclass. Class [[super]] is bound into    *)
(*  user-defined instance methods, and class    *)
(*  [[superMeta]] is bound into user-defined class *)
(*  methods, to guarantee that messages sent to *)
(*  [[SUPER]] from within these methods arrive at the *)
(*  proper destination.                         *)
(*   * Function [[addMethodDefn]] processes each method *)
(*  definition, adding it either to the list of class *)
(*  methods or to the list of instance methods for *)
(*  the new class. We use [[foldr]] to accumulate *)
(*  these lists and place them in [[imethods]] and *)
(*  [[cmethods]].                               *)
(*                                              *)
(* <boxed values 18>=                           *)
val _ = op primitiveMethod : name -> method
  in  (metaclass, CLASSREP class)
  end
(* <evaluation ((usm))>=                        *)
and findClass (supername, xi) =
  case !(find (supername, xi))
    of (meta, CLASSREP c) => (meta, c)
     | v => raise RuntimeError ("object " ^ supername ^ " = " ^ valueString v ^
                                " is not a class")
(* <evaluation ((usm))>=                        *)
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
(* <evaluation ((usm))>=                        *)
and doVal echo (name, value, xi)  =
      ( (find (name, xi) := value; xi)
        handle NotFound _ => bind (name, ref value, xi)
      )
      before printValue echo xi value
(* Unlike our other interpreters, our uSmalltalk *)
(* interpreter doesn't need special-case code to print *)
(* top-level expressions differently from [[val]] *)
(* bindings. In uSmalltalk, every value is printed by *)
(* using its [[print]] method, which you can redefine. *)
(* Because a print method writes directly to standard *)
(* output, we have to define [[echo]] to be a Boolean, *)
(* not a function as in other interpreters.     *)
(* <evaluation ((usm))>=                        *)
and printValue echo xi v = 
  if echo then
    ( eval (SEND (nullsrc, "print", VALUE v, []), emptyEnv, objectClass, xi)
    ; print "\n"
    )
  else
    ()
(* The source location [[nullsrc]] identifies the *)
(* [[SEND]] as something generated internally, rather *)
(* than read from a file or a list of strings.  *)

(* The read-eval-print loop                     *)
(*                                              *)
(* uSmalltalk's read-eval-print loop differs from others *)
(* in two ways:                                 *)
(*                                              *)
(*   * If an error occurs, we call [[showStackTrace]] *)
(*  and [[resetTrace]] before continuing.       *)
(*   * Before each top-level evaluation, we call *)
(*  [[closeLiteralsCycle]]. This call updates the *)
(*  definitions (if any) of [[SmallInteger]],   *)
(*  [[Symbol]], and [[Array]]. By updating these *)
(*  definitions, we make it possible for you to *)
(*  change the behavior of these classes (as is *)
(*  required in Exercises [->], [->], [->], and [->] *)
(*  ).                                          *)
(*                                              *)
(* While the initial basis is being read, calls to *)
(* [[closeLiteralsCycle]] and [[closeBlocksCycle]] fail. *)
(* We ignore these failures, but once initialization is *)
(* complete, these cycles are closed by the code in *)
(* chunk [->], which catches failures. [*]      *)
(* <evaluation ((usm))>=                        *)
and readEvalPrint (defs : def stream, echo, errmsg) xi =
  let fun processDef (def, xi) =
        let fun continue msg = (errmsg msg; showStackTrace (); resetTrace (); xi
                                                                               )
            val _ = (closeLiteralsCycle xi; closeBlocksCycle xi)
                    handle NotFound _ => ()
            in  evaldef (def, echo, xi)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* <more read-eval-print handlers ((usm))>=     *)
                | Subscript       => continue ("array subscript out of bounds")
                | Size            => continue ("bad array size")
                (* The next handlers deal with problems that arise *)
                (* during I/O, lexical analysis, and parsing.   *)
                (* <more read-eval-print handlers>=             *)
                (* The exception [[IO.Io]] is part of the Standard Basis *)
                (* Library.                                     *)

                (* The remaining handlers deal with problems that arise *)
                (* during evaluation.                           *)
                (* <more read-eval-print handlers>=             *)
                | Div               => continue "Division by zero"
                | Overflow          => continue "Arithmetic overflow"
                | RuntimeError msg  => continue ("run-time error: " ^ msg)
                | NotFound n        => continue ("variable " ^ n ^ " not found")
                (* Exceptions [[Div]] and [[Overflow]] are predefined. *)

            end
  in  streamFold processDef xi (defs : def stream)
  end
(* The object named as a superclass must in fact *)
(* represent a class, so its representation must be *)
(* [[CLASSREP c]], where [[c]] is the class it  *)
(* represents. That object is an instance of its *)
(* metaclass. Function [[findClass]] returns the *)
(* metaclass and the class.                     *)
(* <boxed values 19>=                           *)
val _ = op findClass : name * value ref env -> class * class
(* Evaluating definitions                       *)
(*                                              *)
(* Evaluating a definition computes a new global *)
(* environment. In a [[VAL]] binding, the right-hand *)
(* side is evaluated as if in the context of a message *)
(* sent to a value of class [[Object]]. As usual, a *)
(* top-level expression is syntactic sugar for a binding *)
(* to [[it]]. [[DEFINE]] is syntactic sugar for a *)
(* definition of block. Evaluating a class definition *)
(* binds a new class object, as described above. *)
(* <boxed values 19>=                           *)
val _ = op evaldef : def * bool * value ref env -> value ref env
(* The [[]]                                     *)
(* include the handlers used in micro-Scheme. We add *)
(* handlers for the Standard ML exceptions [[Subscript]] *)
(* and [[Size]], which may be raised by array   *)
(* primitives.                                  *)



(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION                                              *)
(*                                                               *)
(*****************************************************************)

(* Initializing, bootstrapping, and running the *)
(* interpreter                                  *)
(*                                              *)
(* The first step in creating the initial environment is *)
(* to add the built-in classes. Each one needs a *)
(* metaclass to be an instance of. To be faithful to *)
(* Smalltalk, the subclass relationships of the *)
(* metaclasses should be isomorphic to the subclass *)
(* relationships of the classes. This is true for the *)
(* user-defined classes created with [[newClassObject]], *)
(* but on the built-in classes, we cheat: the   *)
(* metaclasses for [[UndefinedObject]] and [[Class]] *)
(* inherit directly from [[Class]], not from [[Object]] *)
(* 's metaclass.                                *)
(* <initialization ((usm))>=                    *)
val initialXi = emptyEnv

fun mkMeta c = mkClass ("class " ^ className c) classClass [] []
fun addClass (c, xi) = bind (className c, ref (mkMeta c, CLASSREP c), xi)
val initialXi = foldl addClass initialXi [ objectClass, nilClass, classClass ]
(* The next step is to read the class definitions in the *)
(* initial basis. For debugging, it can be helpful to *)
(* set [[echoBasis]] to [[true]].               *)
(* <initialization ((usm))>=                    *)
val echoBasis = false
val initialXi =
  let val defs = reader smalltalkSyntax noPrompts
                 ("initial basis", streamOfList (* Further reading
                                                                              *)
                                                (*
                                                                              *)
                                                (* Fat book by \citetaho-ullman:
                                                              theory-parsing. *)
                                                (*
                                                                              *)
                                                (* Really nice paper by \
                                                       citetknuth:left-right. *)
                                                (*
                                                                              *)
                                                (* \citetwirth:unnecessary-
                                                      diversity master of the *)
                                                (* hand-written recursive-
                                                        descent parser.       *)
                                                (*
                                                                              *)
                                                (* \citetgibbons:under-
                                                     appreciated-unfold       *)
                                                (*
                                                                              *)
                                                (* \citetramsey:spurious-error
                                                                              *)
                                                (*
                                                                              *)
                                                (* [cite mcbride-paterson:
                                                        applicative]          *)
                                                (* <ML representation of initial
                                                               basis>=        *)

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
(* Before we can close the cycles, we have to create *)
(* [[VAL]] bindings for [[true]] and [[false]]. Because *)
(* the parser prevents user code from binding [[true]] *)
(* and [[false]], we can't do this in uSmalltalk; the *)
(* bindings have to be added in ML.             *)
(* <initialization ((usm))>=                    *)
local 
  fun newInstance classname = SEND (nullsrc, "new", VAR classname, [])
in
  val initialXi = evaldef (VAL ("true",  newInstance "True" ), false, initialXi)
  val initialXi = evaldef (VAL ("false", newInstance "False"), false, initialXi)
end
(* Once we've read the class definitions, we can close *)
(* the cycles, update the ref cells, and we're almost *)
(* ready to go. By this time, all the necessary classes *)
(* must be defined, so if any cycle fails to close, we *)
(* halt the interpreter with a fatal error. [*] *)
(* <initialization ((usm))>=                    *)
val _ =
  ( closeLiteralsCycle initialXi
  ; closeBooleansCycle initialXi
  ; closeBlocksCycle   initialXi
  ) handle NotFound n =>
      ( app print ["Fatal error: ", n, " is not defined in the initial basis\n"]
      ; raise InternalError "this can't happen"
      )
  | e => ( print "Error binding basis classes into interpreter\n"; raise e)
(* The last step initialization is to bind predefined *)
(* values. The value [[nil]] is bound here because the *)
(* parser won't let us create a [[val]] binding for it. *)
(* The other values are symbols that are useful for *)
(* printing, but that can't be expressed using  *)
(* uSmalltalk's literal symbol notation.        *)
(* <initialization ((usm))>=                    *)
fun addVal ((name, v), xi) = evaldef (VAL (name, VALUE v), false, xi)
val initialXi = foldl addVal initialXi
  [ ("nil", nilValue)
  , ("lparen",  mkSymbol "("),  ("rparen", mkSymbol ")")
  , ("lbrack",  mkSymbol "["),  ("rbrack", mkSymbol "]")
  , ("newline", mkSymbol "\n"), ("space",  mkSymbol " ")
  ]
(* <initialization ((usm))>=                    *)
fun runInterpreter noisy = 
  let val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader smalltalkSyntax prompts ("standard input", streamOfLines
                                                                   TextIO.stdIn)
      fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
  in  ignore (readEvalPrint (defs : def stream, true, errorln) initialXi)
  end 
(* The function [[runInterpreter]] takes one argument, *)
(* which tells it whether to prompt.            *)
(* <boxed values 20>=                           *)
val _ = op runInterpreter : bool -> unit


(*****************************************************************)
(*                                                               *)
(*   COMMAND LINE                                                *)
(*                                                               *)
(*****************************************************************)

(* Building and exporting a program             *)
(*                                              *)
(* The final step in implementing the interpreter is to *)
(* create a function that looks at the command line and *)
(* calls [[runInterpreter]]. With a compiler like *)
(* Moscow ML or MLton, the module isn't elaborated until *)
(* run time, so we can simply insert an irrelevant *)
(* [[val]] binding, the elaboration of which has the *)
(* side effect of calling [[main]].             *)
(* [[CommandLine.arguments ()]] returns an argument *)
(* list.                                        *)
(* <command line>=                              *)
fun main ["-q"] = runInterpreter false
  | main []     = runInterpreter true
  | main _      =
      TextIO.output (TextIO.stdErr, "Usage: " ^ CommandLine.name () ^ " [-q]\n")
val _ = main (CommandLine.arguments ())
