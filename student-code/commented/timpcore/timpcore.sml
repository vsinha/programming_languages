(* Putting all the pieces together              *)
(*                                              *)
(* We stitch together the parts of the implementation in *)
(* this order:                                  *)
(* <timpcore.sml>=                              *)


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
(* <boxed values 15>=                           *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* Because ML strings are immutable, we can use them to *)
(* represent names directly. We also use exceptions, not *)
(* an [[error]] procedure, to indicate when things have *)
(* gone wrong. The exceptions we use are listed in *)
(* Table [->].                                  *)

exception LeftAsExercise of string


(*****************************************************************)
(*                                                               *)
(*   TYPES FOR \TIMPCORE                                         *)
(*                                                               *)
(*****************************************************************)

(* Abstract syntax, types, and values of Typed Impcore *)
(*                                              *)
(* As in Chapter [->], we define the abstract syntax of *)
(* Typed Impcore by presenting the representations we *)
(* use in our implementation. The type system is so *)
(* simple that we use [[ty]] not only as the abstract *)
(* syntax for types but also as the internal    *)
(* representation of types. The type [[funty]]  *)
(* represents the type of a function in Typed Impcore; *)
(* there is no corresponding abstract syntax. [*] *)
(* <types for \timpcore>=                       *)
datatype ty    = INTTY | BOOLTY | UNITTY | ARRAYTY of ty
datatype funty = FUNTY of ty list * ty
(* Any representation of type [[funty]] describes one *)
(* type; for example, the comparison functions all have *)
(* a type that says ``two integer arguments and a *)
(* Boolean result.'' A language in which a name has at *)
(* most one type is called monomorphic.         *)

(* <types for \timpcore>=                       *)
(* <printing types for \timpcore>=              *)
fun typeString BOOLTY        = "bool"
  | typeString INTTY         = "int"
  | typeString UNITTY        = "unit"
  | typeString (ARRAYTY tau) = "(array " ^ typeString tau ^ ")"
(* <types for \timpcore>=                       *)
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

(* <lexical analysis ((mlscheme))>=             *)
datatype token = NAME    of string
               | INT     of int
               | SHARP   of bool
               | BRACKET of char (* ( or ) *)
               | QUOTE
(* I define [[isLiteral]] by comparing the given string  *)
(* [[s]] with the string form of token [[t]].   *)

(* <lexical analysis ((mlscheme))>=             *)
fun tokenString (NAME x)    = x
  | tokenString (INT  n)    = Int.toString n
  | tokenString (SHARP b)   = if b then "#t" else "#f"
  | tokenString (BRACKET c) = str c
  | tokenString (QUOTE)     = "'"

fun isLiteral s t = tokenString t = s
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
(* <boxed values 26>=                           *)
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
(* <boxed values 27>=                           *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a streams is read, no new actions are performed. *)
(* <boxed values 27>=                           *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* <boxed values 28>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such stream, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 28>=                           *)
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
(* <boxed values 29>=                           *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* <streams>=                                   *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 30>=                           *)
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
(* <boxed values 31>=                           *)
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
(* <boxed values 32>=                           *)
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
(* <boxed values 33>=                           *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* <boxed values 33>=                           *)
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
(* <boxed values 34>=                           *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 35>=                           *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right: [*]                                   *)
(* <boxed values 36>=                           *)
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
(* <boxed values 37>=                           *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 37>=                           *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 38>=                           *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 39>=                           *)
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
(* <boxed values 40>=                           *)
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
(* <boxed values 41>=                           *)
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
(* <boxed values 42>=                           *)
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
(* <boxed values 42>=                           *)
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
(* <boxed values 43>=                           *)
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
(* <boxed values 44>=                           *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* has a special operator [[<>]], which is also *)
(* pronounced ``applied to.'' It combines a B-to-C *)
(* function with an \atob transformer to produce an \ *)
(* atoc transformer.                            *)
(* <boxed values 45>=                           *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* <boxed values 46>=                           *)
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
(* <boxed values 47>=                           *)
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
(* <boxed values 48>=                           *)
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
(* <boxed values 49>=                           *)
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
(* <boxed values 50>=                           *)
val _ = op eos : ('a, unit) xformer
(* <parsing combinators>=                       *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* It can also be useful to peek at the contents of a *)
(* stream, without looking at any input, and while *)
(* ignoring errors.                             *)
(* <boxed values 51>=                           *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* <parsing combinators>=                       *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* And we might want to transform some input, then *)
(* rewind it back to the starting point. (Actions can't *)
(* be undone, but at least the input can be read again.) *)
(* <boxed values 52>=                           *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* <boxed values 53>=                           *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun oneEq x = sat (fn x' => x = x') one
(* <boxed values 54>=                           *)
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
(* <boxed values 55>=                           *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* <boxed values 56>=                           *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* <boxed values 57>=                           *)
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
(* <boxed values 58>=                           *)
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
(* <boxed values 59>=                           *)
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
(* <boxed values 60>=                           *)
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
(* <boxed values 61>=                           *)
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
(* <boxed values 62>=                           *)
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
(* <boxed values 63>=                           *)
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
(* <boxed values 64>=                           *)
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
(* <boxed values 65>=                           *)
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
(* <boxed values 66>=                           *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* <boxed values 67>=                           *)
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
(* <boxed values 68>=                           *)
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
(* <boxed values 68>=                           *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To signal an error at a given location, call *)
(* [[errorAt]].                                 *)
(* <boxed values 68>=                           *)
val _ = op errorAt : string -> srcloc -> 'a error
(* We can pair source-code locations with individual *)
(* lines and tokens. To make it easier to read the *)
(* types, I define a type abbreviation which says that a *)
(* value paired with a location is ``located.'' *)
(* <boxed values 68>=                           *)
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
(* <boxed values 69>=                           *)
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
(* <boxed values 70>=                           *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <boxed values 70>=                           *)
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
(* <boxed values 70>=                           *)
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
(* <boxed values 71>=                           *)
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
(* <boxed values 72>=                           *)
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
(* <boxed values 73>=                           *)
val _ = op <!> : 'a parser * string -> 'b parser
(* Keywords, brackets, and other literals       *)
(*                                              *)
(* It's extremely common to want to recognize literal *)
(* tokens, like the keyword [[if]] or a left or right *)
(* parenthesis. The [[literal]] parser accepts any token *)
(* whose concrete syntax is an exact match for the given *)
(* string argument.                             *)
(* <boxed values 73>=                           *)
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
(* <boxed values 74>=                           *)
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
(* <boxed values 75>=                           *)
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
(* <boxed values 76>=                           *)
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
(* <boxed values 77>=                           *)
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
(* <boxed values 78>=                           *)
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
(* <boxed values 79>=                           *)
val _ = op echoTagStream : line stream -> line stream 
(* <an interactive reader>=                     *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* Lexing and parsing with error handling       *)
(*                                              *)
(* The next step is error handling. When the code *)
(* detects an error it prints a message using function *)
(* [[errorln]].                                 *)
(* <boxed values 80>=                           *)
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
(* <boxed values 81>=                           *)
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
(* <boxed values 82>=                           *)
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
(* <boxed values 83>=                           *)
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
(* <boxed values 84>=                           *)
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
(* <boxed values 85>=                           *)
val _ = op reader : token lexer * 'a parser -> prompts -> string * line stream
                                                                    -> 'a stream
val _ = op lexAndDecorate : srcloc * line -> token located inline stream
  in  
      stripErrors (preStream (setPrompt ps1, edefs))
  end 
(* Supporting code for the ML interpreter for \uscheme *)
(*                                              *)
(* [*] [*]                                      *)
(*                                              *)
(* Tokens of the micro-Scheme language          *)
(*                                              *)
(* Our general parsing mechanism from Appendix [->] *)
(* requires us to define a [[token]] type and two *)
(* functions [[tokenString]] and [[isLiteral]]. *)

(* The abstractions are useful for reading all kinds of *)
(* input, not just computer programs, and I encourage *)
(* you to use them in your own projects. But here are *)
(* two words of caution: with so many abstractions in *)
(* the mix, the parsers are tricky to debug. And while *)
(* some parsers built from combinators are very *)
(* efficient, mine aren't.                      *)

(* <lexical analysis ((mlscheme))>=             *)
local
  (* The [[atom]] function identifies the special literals *)
  (* [[#t]] and [[#f]]; all other atoms are names. *)
  (* <functions used in the lexer for \uscheme>=  *)
  fun atom "#t" = SHARP true
    | atom "#f" = SHARP false
    | atom x    = NAME x
  (* <functions used in the lexer for \uscheme>=  *)
  fun noneIfLineEnds chars =
    case streamGet chars
      of NONE => NONE (* end of line *)
       | SOME (#";", cs) => NONE (* comment *)
       | SOME (c, cs) => 
           let val msg = "invalid initial character in `" ^
                         implode (c::listOfStream cs) ^ "'"
           in  SOME (ERROR msg, EOS)
           end
  (* If the lexer doesn't recognize a bracket, quote mark, *)
  (* integer, or other atom, we're expecting the line to *)
  (* end. The end of the line may present itself as the *)
  (* end of the input stream or as a stream of characters *)
  (* beginning with a semicolon, which marks a comment. *)
  (* If we encounter any other character, something has *)
  (* gone wrong. (The polymorphic type of         *)
  (* [[noneIfLineEnds]] provides a subtle but powerful *)
  (* hint that no token can be produced; the only possible *)
  (* outcomes are that nothing is produced, or the lexer *)
  (* detects an error.) [*]                       *)
  (* <boxed values 87>=                           *)
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
(* Before a micro-Scheme token, whitespace is ignored. *)
(* The [[schemeToken]] function enumerates the  *)
(* alternatives: two brackets, a quote mark, an integer *)
(* literal, an atom, or end of line. [*]        *)
(* <boxed values 86>=                           *)
val _ = op schemeToken : token lexer
val _ = op atom : string -> token
end


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR \TIMPCORE                    *)
(*                                                               *)
(*****************************************************************)

(* There|width 0pt height 11pt are two kinds of value: *)
(* [[NUM]], which represents both integers and Booleans, *)
(* and [[ARRAY]], which represents arrays.      *)
(* <abstract syntax and values for \timpcore>=  *)
datatype value = NUM   of int
               | ARRAY of value array
(* The abstract syntax of expressions is more   *)
(* complicated than what you would expect for Impcore. *)
(* The reason is that in Typed Impcore, the primitives *)
(* [[=]] and [[print]] cannot be represented as *)
(* functions, because they operate on values of more *)
(* than one type: they are polymorphic. In a monomorphic *)
(* language like Typed Impcore, polymorphic primitives *)
(* require their own abstract syntax. Similarly, as *)
(* described in Section [->], array operations require *)
(* special abstract syntax.                     *)
(* <abstract syntax and values for \timpcore>=  *)
datatype exp   = LITERAL of value
               | VAR     of name
               | SET     of name * exp
               | IFX     of exp * exp * exp
               | WHILEX  of exp * exp
               | BEGIN   of exp list
               | EQ      of exp * exp
               | PRINT   of exp
               | APPLY   of name * exp list
               (* As required by the specification, the [[array-get]] *)
               (* operation is quite flexible. In the last example, the *)
               (* [[array-get]] operation takes an argument of type *)
               (* [[(array int)]] and returns a result of type [[int]], *)
               (* but in the example before that, it takes an argument *)
               (* of type [[(array (array int))]] and returns a result *)
               (* of type [[(array int)]]. No mere function in Typed *)
               (* Impcore can do such things; this behavior is *)
               (* polymorphic. Typed Impcore is monomorphic, which *)
               (* means that each function can be used for arguments *)
               (* and results of one and only one type. This means we *)
               (* can't just put [[array-get]] into the initial basis *)
               (* for Typed Impcore; we have to make it a special *)
               (* operation in the abstract syntax. In fact, all of the *)
               (* array operations are polymorphic, so we have to add *)
               (* these expressions to the abstract syntax:    *)
               (* <array extensions to \timpcore's abstract syntax>= *)
               | AGET  of exp * exp
               | ASET  of exp * exp * exp
               | AMAKE of exp * exp
               | ALEN  of exp
               (* This example illustrates a general principle: in a *)
               (* monomorphic language, polymorphic primitives require *)
               (* special abstract syntax. This principle also applies *)
               (* to C and C++, for example, which denote array *)
               (* operations with special syntax involving square *)
               (* brackets.                                    *)

(* These changes are typical for this kind of design: in *)
(* a monomorphic language, each polymorphic operation *)
(* requires special abstract syntax, as opposed to just *)
(* a built-in function. In C, for example, it is not *)
(* possible to write a general function that can *)
(* dereference a pointer of any type; instead, one uses *)
(* the special [[*]] syntax.                    *)

(* In Typed Impcore, the abstract syntax for a function *)
(* definition requires that the result type and the *)
(* types of the formal parameters be identified *)
(* explicitly. The concrete syntax puts types on the *)
(* left, by analogy with C. The abstract syntax puts *)
(* types on the right, as is customary in formal *)
(* semantics and in Pascal-like and ML-like languages. *)
(* <abstract syntax and values for \timpcore>=  *)
type userfun = { formals : (name * ty) list, body : exp, returns : ty }
datatype def = VAL    of name * exp
             | EXP    of exp
             | DEFINE of name * userfun
             | USE    of name
(* In Typed Impcore, the function name in an application *)
(* is not an ordinary value, so it can't stand for *)
(* something of type [[value]] in our implementation. In *)
(* Chapter [->], we represent Impcore functions using *)
(* the C type [[Fun]], but [[fun]] is a reserved word *)
(* in ML, so we use the name [[func]] instead. As in our *)
(* interpreter for micro-Scheme, a primitive function is *)
(* represented as an ML function.               *)
(* <abstract syntax and values for \timpcore>=  *)
datatype func = USERDEF   of string list * exp
              | PRIMITIVE of value list -> value
(* There are no types in the representation of [[func]]; *)
(* types are needed only during type checking, and the *)
(* [[func]] representation is used at run time, after *)
(* all types have been checked.                 *)

(* <abstract syntax and values for \timpcore>=  *)
(* It would be good to figure out how to use    *)
(* [[separate]] in this code.                   *)
(* <printing values for \timpcore>=             *)
fun valueString (NUM n) = Int.toString n
  | valueString (ARRAY a) =
      if Array.length a = 0 then
          "[]"
      else
          let val elts = Array.foldr (fn (v, s) => " " :: valueString v :: s) [
                                                                          "]"] a
          in  String.concat ("[" :: tl elts)
          end
(* Appendix [->] defines a function used to print types. *)
(* <boxed values 1>=                            *)
val _ = op typeString : ty -> string
(* We define two functions that compare types for *)
(* equality.                                    *)
(* <boxed values 1>=                            *)
val _ = op eqType  : ty      * ty     -> bool
val _ = op eqTypes : ty list * ty list -> bool
(* Just like types, values can be printed. The code *)
(* appears in Appendix [->].                    *)
(* <boxed values 1>=                            *)
val _ = op valueString : value -> string
(* <abstract syntax and values for \timpcore>=  *)
exception BugInTypeChecking of string
fun toArray (ARRAY a) = a
  | toArray _         = raise BugInTypeChecking "non-array value"
fun toInt   (NUM n)   = n
  | toInt _           = raise BugInTypeChecking "non-integer value"
(* To interpret any array operation, we need to convert *)
(* at least one argument from a [[value]] to an array or *)
(* to an integer. If the program type checks, the *)
(* conversion should always succeed; if a conversion *)
(* fails, there is a bug in the type checker. The *)
(* [[toArray]] and [[toInt]] functions do the job. *)
(* <boxed values 7>=                            *)
val _ = op toArray : value -> value array
val _ = op toInt   : value -> int


(*****************************************************************)
(*                                                               *)
(*   PARSING FOR \TIMPCORE                                       *)
(*                                                               *)
(*****************************************************************)

(* Parsing                                      *)
(*                                              *)
(* Typed Impcore can use micro-Scheme's lexical *)
(* analysis, so all we have here is a parser.   *)
(* <parsing for \timpcore>=                     *)
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
(* <parsing for \timpcore>=                     *)
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
(* <parsing for \timpcore>=                     *)
val timpcoreSyntax = (schemeToken, def)


(*****************************************************************)
(*                                                               *)
(*   IMPLEMENTATION OF [[USE]]                                   *)
(*                                                               *)
(*****************************************************************)

(* The implementation of [[use]] is parameterized by *)
(* [[readEvalPrint]] and [[syntax]] so we can share it *)
(* with other interpreters. Function [[use]] creates a *)
(* reader that does not prompt, but it uses [[writeln]] *)
(* to be sure that responses are printed.       *)
(* <implementation of [[use]]>=                 *)
fun use readEvalPrint syntax filename rho =
      let val fd = TextIO.openIn filename
          val defs = reader syntax noPrompts (filename, streamOfLines fd)
          fun writeln s = app print [s, "\n"]
          fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      in  readEvalPrint (defs, writeln, errorln) rho
          before TextIO.closeIn fd
      end 
(* Functions [[reader]] and [[streamOfLines]] are *)
(* defined in Appendix [->]. They are based on an *)
(* abstraction called streams. A stream is like a list, *)
(* except that when client code first looks at an *)
(* element of a stream, the stream abstraction may do *)
(* some input or output. Function [[streamOfLines]] *)
(* produces a stream containing the lines of source code *)
(* found in the named file. Function \monoreader syntax *)
(* noPrompts converts that stream into a stream of *)
(* definitions.                                 *)



(*****************************************************************)
(*                                                               *)
(*   TYPE CHECKING FOR \TIMPCORE                                 *)
(*                                                               *)
(*****************************************************************)

(* <type checking for \timpcore>=               *)
exception TypeError of string
fun typeof (e, globals, functions, formals) =
  let (* All literals are integers. \usetyLiteral     *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
      fun ty (LITERAL v) = INTTY
      (* To type a variable, we must try two environments. \ *)
      (* usetyFormalVar \usetyGlobalVar The code is shorter *)
      (* than the rules!                              *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
        | ty (VAR x)     = (find (x, formals) handle NotFound _ => find (x,
                                                                       globals))
      (* If the variable is not found in either \rgam or \vgam *)
      (* , the type checker raises the [[NotFound]] exception. *)
      (*                                              *)

      (* We also need two environments to check assignments. \ *)
      (* usetyFormalAssign \usetyGlobalAssign To implement *)
      (* these rules, we determine the types of the variable *)
      (* and the expression, then compare for equality. (The *)
      (* recursive call [[ty (VAR x)]] is a short cut that *)
      (* avoids duplicating code.) Giving an error message *)
      (* that is even remotely helpful requires as much code *)
      (* as checking the types.                       *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
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
      (* The premises of the \rulenameIf rule require both *)
      (* branches to have the same type. \usetyIf The *)
      (* implementation computes the types of the conditions *)
      (* and both branches. Again, most of the code is devoted *)
      (* to error messages.                           *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
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
      (* The checking of a [[while]] loop is very similar to *)
      (* that of an [[if]], except that we don't care what the *)
      (* type of the body is. \usetyWhile             *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
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
      (* The code for [[begin]] checks the types of all *)
      (* sub-expressions. \usetyBegin \usetyEmptyBegin We *)
      (* handle the \rulenameEmptyBegin rule by using *)
      (* [[UNITTY]] as the initial value of [[tau]] that is *)
      (* passed to [[last]].                          *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
        | ty (BEGIN es) =
             let val bodytypes = map ty es
                 fun last tau []     = tau
                   | last tau (h::t) = last h t
             in  last UNITTY bodytypes
             end
      (* Because the two polymorphic primitives have special *)
      (* rules, they require special code in the type checker. *)
      (* \usetyApplyEq Because functions in Typed Impcore are *)
      (* called by name, we can identify the equality *)
      (* primitive by name.                           *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
        | ty (EQ (e1, e2)) =
             let val (tau1, tau2) = (ty e1, ty e2)
             in  if eqType (tau1, tau2) then
                   BOOLTY
                 else
                   raise TypeError (
                                "Equality compares values of different types " ^
                                    typeString tau1 ^ " and " ^ typeString tau2)
             end
      (* The [[print]] primitive is similar. \usetyApplyPrint *)
      (* We must check the type of the argument even though it *)
      (* doesn't affect the type of the result.       *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
        | ty (PRINT e) = (ty e; UNITTY)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$>=
                                                                              *)
        | ty (APPLY (f, actuals)) =
             let val actualtypes                     = map ty actuals
                 val FUNTY (formaltypes, resulttype) = find (f, functions)
                 (* <definition of [[parameterError]]>=          *)
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
                 (* For the general case of function application, we look *)
                 (* up the function in the appropriate environment. *)
                 (* To issue a decent error message, we compare the types *)
                 (* of the actual and formal parameters one by one. \ *)
                 (* usetyApply                                   *)
                 (* <boxed values 3>=                            *)
                 val _ = op parameterError : int * ty list * ty list -> 'a
             in  if eqTypes (actualtypes, formaltypes) then
                   resulttype
                 else
                   parameterError (1, actualtypes, formaltypes)
             end
      (* We don't show you how to turn these rules into code *)
      (* for the type checker; that problem is left for *)
      (* Exercise [->]. [*]                           *)
      (* <function [[ty]], to check the type of an expression, given $\itenvs$ (
                                                               (prototype))>= *)
      | ty (AGET (a, i))       = raise LeftAsExercise "AGET"
      | ty (ASET (a, i, e))    = raise LeftAsExercise "ASET"
      | ty (AMAKE (len, init)) = raise LeftAsExercise "AMAKE"
      | ty (ALEN a)            = raise LeftAsExercise "ALEN"
(* Type checking                                *)
(*                                              *)
(* Given an expression e and a collection of type *)
(* environments \xgam, \fgam, and \rgam, calling typeof *)
(* (e, \xgam, \fgam, \rgam) returns a type tau such that *)
(* \itypeise tau. If no such type exists, [[typeof]] *)
(* raises the [[TypeError]] exception (or possibly *)
(* [[NotFound]]). We use an auxiliary, nested function  *)
(* [[ty]], which doesn't pass environments explicitly. *)
(* <boxed values 2>=                            *)
val _ = op typeof  : exp * ty env * funty env * ty env -> ty
val _ = op ty      : exp -> ty
  in  ty e
  end
(* Just as we can derive an implementation of [[eval]] *)
(* by examining the rules of operational semantics, we *)
(* can derive an implementation of [[ty]] by examining *)
(* the rules of the type system. To help show the *)
(* connection between the type system and the type *)
(* checker, we show the relevant rules before each case *)
(* of the function [[ty]].                      *)

(* <type checking for \timpcore>=               *)
exception RuntimeError of string
fun elabdef (d, globals, functions) =
    case d
      of (* Elaborating a [[val]] binding requires extending the *)
         (* global-variable environment. \usetyVal       *)
         (* <cases for elaborating definitions in \timpcore>= *)
           VAL (x, e) => (bind (x, typeof (e, globals, functions, emptyEnv),
                                                            globals), functions)
         (* A top-level expression is syntactic sugar for a *)
         (* definition of [[it]]. \usetyExp              *)
         (* <cases for elaborating definitions in \timpcore>= *)
         | EXP e => elabdef (VAL ("it", e), globals, functions)
         (* A function definition requires significant   *)
         (* manipulation of the function environment. \usety *)
         (* Define                                       *)
         (* <cases for elaborating definitions in \timpcore>= *)
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
         (* A [[use]] directive should never get this far. *)
         (* <cases for elaborating definitions in \timpcore>= *)
         | USE _ => raise BugInTypeChecking "`use' reached the type checker"
(* Type-checking definitions                    *)
(*                                              *)
(* The form of the typing judgment for a definition d is *)
(* \itoptd -->\stwo\fgamp\vgamp. The process of *)
(* type-checking a definition and extending the type *)
(* environments is called elaboration.          *)
(* <boxed values 4>=                            *)
val _ = op elabdef : def * ty env * funty env -> ty env * funty env


(*****************************************************************)
(*                                                               *)
(*   CHECKING AND EVALUATION FOR \TIMPCORE                       *)
(*                                                               *)
(*****************************************************************)

(* <checking and evaluation for \timpcore>=     *)
(* <evaluation for \timpcore>=                  *)
(* <definition of [[eval]] for \timpcore>=      *)
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
                | USERDEF func => (* <apply user-defined function [[func]] to
                                                                   [[args]]>= *)
                                  let val (formals, body) = func
                                      val actuals         = map (ref o ev) args
                                  (* To apply a function, we build an evaluation
                                                                              *)
                                  (* environment. We strip the types off the
                                                                  formals and *)
                                  (* we put the actuals in mutable ref cells.
                                                                              *)
                                  (* <boxed values 10>=
                                                                              *)
                                  val _ = op formals : name      list
                                  val _ = op actuals : value ref list
                                  in  eval (body, globals, functions, bindList (
                                                    formals, actuals, emptyEnv))
                                      handle BindListLength => 
                                          raise BugInTypeChecking
                                         "Wrong number of arguments to function"
                                  end)
        (* <more alternatives for [[ev]] for \timpcore>= *)
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
        (* Once we have [[toArray]] and [[toInt]], interpreting *)
        (* the array operations is easy. Everything we need is *)
        (* in the [[Array]] module from ML's Standard Basis *)
        (* Library. The library includes run-time checks for bad *)
        (* subscripts or array sizes; we need these checks *)
        (* because Typed Impcore's type system is not powerful *)
        (* enough to preclude such errors.              *)
        (* <boxed values 8>=                            *)
        val _ = op ev : exp -> value
        (* When we build the interpreter from this book, this *)
        (* code becomes part of the evaluator in Appendix [->]. *)

(* Evaluation                                   *)
(*                                              *)
(* <boxed values 9>=                            *)
val _ = op ev : exp -> value
  in  ev e
  end
(* The implementation of the evaluator uses the same *)
(* techniques we use to implement micro-Scheme in *)
(* Chapter [->]. Because of Typed Impcore's many *)
(* environments, the evaluator does more bookkeeping. *)
(* Another difference is that many potential run-time *)
(* errors should be impossible because the relevant code *)
(* would be rejected by the type checker. If one of *)
(* those errors occurs anyway, we raise the exception *)
(* [[BugInTypeChecking]].                       *)
(* <boxed values 11>=                           *)
val _ = op eval : exp * value ref env * func env * value ref env -> value
(* <evaluation for \timpcore>=                  *)
fun evaldef (d, globals, functions, echo) =
  case d
    of VAL (name, e) => (* <evaluate [[e]] and bind to [[name]]>=       *)
                        let val v = eval (e, globals, functions, emptyEnv)
                            val _ = echo (valueString v)
                        in  (bind (name, ref v, globals), functions)
                        end
     | EXP e => evaldef (VAL ("it", e), globals, functions, echo)
     | DEFINE (f, {body=e, formals=xs, returns=rt}) =>
          (globals, bind (f, USERDEF (map #1 xs, e), functions))
          before echo f
     | USE _ => raise RuntimeError "Internal error - `use' was evaluated"
(* <evaluation for \timpcore>=                  *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* <boxed values 12>=                           *)
val _ = op evaldef : def * value ref env * func env * (string->unit) -> value
                                                              ref env * func env
(* Here are the primitives. As in Chapter [->], all are *)
(* either binary or unary operators. Type checking *)
(* should guarantee that operators are used with the *)
(* correct arity.                               *)
(* <boxed values 12>=                           *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* <evaluation for \timpcore>=                  *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
val arithtype = FUNTY ([INTTY, INTTY], INTTY)
(* Arithmetic primitives expect and return integers. *)
(* <boxed values 13>=                           *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
val _ = op arithtype : funty
(* As in Chapter [->], we use the chunk [[<<primops for *)
(* Typed Impcore [[::]]>>]] to cons up all the  *)
(* primitives into one giant list, and we use that list *)
(* to build the initial environment for the     *)
(* read-eval-print loop. The big difference is that in *)
(* Typed Impcore, each primitive has a type as well as a *)
(* value.                                       *)

(* <evaluation for \timpcore>=                  *)
fun embedPredicate f args = NUM (if f args then 1 else 0)
fun comparison f = binaryOp (embedPredicate f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")
val comptype = FUNTY ([INTTY, INTTY], BOOLTY)
(* Comparisons take two arguments. Most comparisons *)
(* (except for equality) apply only to integers. *)
(* <boxed values 14>=                           *)
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
(* Top-level processing: type checking and evaluation *)
(*                                              *)
(* In an interpreter for a dynamically typed language *)
(* such as Impcore or micro-Scheme, we can evaluate a *)
(* top-level item as soon as it is parsed. In an *)
(* interpreter for a statically typed language such as *)
(* Typed Impcore, we require a type-checking step *)
(* between parsing and evaluation. A simple way to *)
(* introduce this step is to define a function  *)
(* [[checkThenEval]] which first elaborates a definition *)
(* (type-checking all its subexpressions), then *)
(* evaluates it. This function manipulates not only the *)
(* top-level type environments \fgam and \vgam but also *)
(* the top-level value and function environments phi *)
(*  and xi. We define type [[env_bundle]] to refer to *)
(* this group of four environments. The value   *)
(* environment xi is the only one that can be mutated *)
(* during evaluation, so it is the only one that has a *)
(* [[ref]] in its type.                         *)
(* <boxed values 5>=                            *)
val _ = op checkThenEval : def * env_bundle * (string->unit) -> env_bundle
        in  (tglobals, tfuns, vglobals, vfuns)
        end
(* The distinction between ``compile time,'' where we *)
(* run the type checker [[elabdef]], and ``run time,'' *)
(* where we run the evaluator [[evaldef]], is sometimes *)
(* called the phase distinction. The phase distinction *)
(* is easy to overlook, especially when you're using an *)
(* interactive interpreter or compiler, but the code *)
(* shows the phase distinction is real.         *)

(* <checking and evaluation for \timpcore>=     *)
and readCheckEvalPrint (defs, echo, errmsg) envs =
  let fun processDef (def, envs) =
            let fun continue msg = (errmsg msg; envs)
            in  checkThenEval (def, envs, echo)
                handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
                (* <more read-eval-print handlers>=             *)
                | TypeError         msg => continue ("type error: " ^ msg)
                | BugInTypeChecking msg => continue ("bug in type checking: " ^
                                                                            msg)
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
  in  streamFold processDef envs defs
  end
(* The read-eval-print loop                     *)
(*                                              *)
(* As in micro-Scheme, the read-eval-print loop is *)
(* higher-order. There are two differences: the *)
(* environment parameter's name is [[envs]] instead of *)
(* [[rho]], and we have handlers for new exceptions: *)
(* [[TypeError]] and [[BugInTypeChecking]].     *)
(* <boxed values 6>=                            *)
val _ = op readCheckEvalPrint : def stream * (string->unit) * (string->unit) ->
                                                        env_bundle -> env_bundle
(* The [[]] are the                             *)
(* same handlers used in micro-Scheme. We also have *)
(* handlers for two new exceptions. [[TypeError]] is *)
(* raised not at parsing time, and not at evaluation *)
(* time, but at type-checking time.             *)
(* [[BugInTypeChecking]] should never be raised. *)



(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION FOR \TIMPCORE                                *)
(*                                                               *)
(*****************************************************************)

(* Initializing the interpreter                 *)
(*                                              *)
(* We're ready to put everything together into a working *)
(* interpreter.                                 *)
(* <initialization for \timpcore>=              *)
val initialEnvs =
  let fun addPrim ((name, prim, funty), (tfuns, vfuns)) = 
        ( bind (name, funty, tfuns)
        , bind (name, PRIMITIVE prim, vfuns)
        )
      val (tfuns, vfuns)  = foldl addPrim (emptyEnv, emptyEnv)
                            ((* <primops for \timpcore\ [[::]]>=             *)
                             ("+", arithOp op +,   arithtype) :: 
                             ("-", arithOp op -,   arithtype) :: 
                             ("*", arithOp op *,   arithtype) :: 
                             ("/", arithOp op div, arithtype) ::
                             (* <primops for \timpcore\ [[::]]>=             *)
                             ("<", intcompare op <, comptype) :: 
                             (">", intcompare op >, comptype) :: nil)
      val envs  = (emptyEnv, tfuns, emptyEnv, vfuns)
      val basis = (* Further reading                              *)
                  (*                                              *)
                  (* \citetkoenig:anecdote describes an experience with *)
                  (* ML type inference which leads to a conclusion that *)
                  (* resembles my conclusion about the type of    *)
                  (* [[noneIfLineEnds]] on page [->].             *)
                  (*                                              *)
                  (* <ML representation of initial basis>=        *)

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
(* The code for the primitives appears in Appendix [->]. *)
(* It is similar to the code in Chapter [->], except *)
(* that it supplies a type, not just a value, for each *)
(* primitive.                                   *)
(*                                              *)

(* The function [[runInterpreter]] takes one argument, *)
(* which tells it whether to prompt.            *)
(* <initialization for \timpcore>=              *)
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
