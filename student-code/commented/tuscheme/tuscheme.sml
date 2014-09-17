(* Putting all the pieces together              *)
(*                                              *)
(* We stitch together the parts of the implementation in *)
(* this order:                                  *)
(* <tuscheme.sml>=                              *)


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
(* <boxed values 19>=                           *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* Because ML strings are immutable, we can use them to *)
(* represent names directly. We also use exceptions, not *)
(* an [[error]] procedure, to indicate when things have *)
(* gone wrong. The exceptions we use are listed in *)
(* Table [->].                                  *)

exception TypeError of string


(*****************************************************************)
(*                                                               *)
(*   DEFINITION OF [[SEPARATE]]                                  *)
(*                                                               *)
(*****************************************************************)

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


(*****************************************************************)
(*                                                               *)
(*   TYPES FOR {\TUSCHEME}                                       *)
(*                                                               *)
(*****************************************************************)

(* In our ML code, we represent the abstract syntax of a *)
(* kind using the datatype [[kind]].            *)
(* <types for {\tuscheme}>=                     *)
datatype kind = TYPE                          (* kind of all types *)
              | ARROW of kind list * kind     (* kind of many constructors *)
(* To build types in Typed uScheme, we use not only type *)
(* variables and the \astforall quantifier but also type *)
(* constructors and constructor application. In our *)
(* ML code, we represent the abstract syntax of types *)
(* using the type [[tyex]].                     *)
(* <types for {\tuscheme}>=                     *)
datatype tyex = TYCON  of name                (* type constructor *)
              | CONAPP of tyex * tyex list    (* type-level application *)
              | FORALL of name list * tyex
              | TYVAR  of name                (* type variable *)
(* Because not every combination of type constructors, *)
(* variables, and [[forall]] is actually a type (e.g., *)
(* [[array array]] is not a type), it may be best to *)
(* call such phrases ``type-level expressions.'' When *)
(* we're not being careful, however, we refer to them *)
(* simply as ``types.''                         *)

(* <types for {\tuscheme}>=                     *)
(* <printing types for {\tuscheme}>=            *)
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
(* Throughout the interpreter, we print types using the *)
(* [[typeString]] function from Appendix [->].  *)
(* <boxed values 1>=                            *)
val _ = op typeString : tyex -> string
(* <types for {\tuscheme}>=                     *)
val inttype  = TYCON "int"
val booltype = TYCON "bool"
val symtype  = TYCON "sym"
val unittype = TYCON "unit"
val tyvarA   = TYVAR "'a"
fun tupletype l = CONAPP (TYCON "tuple", l)
fun listtype ty = CONAPP (TYCON "list",[ty])
fun funtype (args, result) = CONAPP (TYCON "function", [tupletype args, result])
(* Standard type constructors of Typed uScheme  *)
(*                                              *)
(* The code above gives representations of and  *)
(* operations on types, but it doesn't make it easy to *)
(* write types. For example, inside the interpreter, the *)
(* type of [[cons]] has to be written using this *)
(* enormous phrase: {smallverbatim} FORALL (["'a"], *)
(* CONAPP (TYCON "function", [CONAPP (TYCON "tuple", *)
(* [TYVAR "'a", CONAPP (TYCON "list", [TYVAR "'a"])]), *)
(* CONAPP (TYCON "list", [TYVAR "'a"])]))       *)
(* {smallverbatim} To make it easier to define the *)
(* primitive operations of Typed uScheme, we provide *)
(* convenience functions.                       *)
(* <boxed values 7>=                            *)
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
(* <boxed values 30>=                           *)
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
(* <boxed values 31>=                           *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a streams is read, no new actions are performed. *)
(* <boxed values 31>=                           *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* <boxed values 32>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such stream, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 32>=                           *)
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
(* <boxed values 33>=                           *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* <streams>=                                   *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 34>=                           *)
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
(* <boxed values 35>=                           *)
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
(* <boxed values 36>=                           *)
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
(* <boxed values 37>=                           *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* <boxed values 37>=                           *)
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
(* <boxed values 38>=                           *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 39>=                           *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right: [*]                                   *)
(* <boxed values 40>=                           *)
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
(* <boxed values 41>=                           *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 41>=                           *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 42>=                           *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 43>=                           *)
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
(* <boxed values 44>=                           *)
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
(* <boxed values 45>=                           *)
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
(* <boxed values 46>=                           *)
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
(* <boxed values 46>=                           *)
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
(* <boxed values 47>=                           *)
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
(* <boxed values 48>=                           *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* has a special operator [[<>]], which is also *)
(* pronounced ``applied to.'' It combines a B-to-C *)
(* function with an \atob transformer to produce an \ *)
(* atoc transformer.                            *)
(* <boxed values 49>=                           *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* <boxed values 50>=                           *)
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
(* <boxed values 51>=                           *)
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
(* <boxed values 52>=                           *)
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
(* <boxed values 53>=                           *)
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
(* <boxed values 54>=                           *)
val _ = op eos : ('a, unit) xformer
(* <parsing combinators>=                       *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* It can also be useful to peek at the contents of a *)
(* stream, without looking at any input, and while *)
(* ignoring errors.                             *)
(* <boxed values 55>=                           *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* <parsing combinators>=                       *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* And we might want to transform some input, then *)
(* rewind it back to the starting point. (Actions can't *)
(* be undone, but at least the input can be read again.) *)
(* <boxed values 56>=                           *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* <boxed values 57>=                           *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun oneEq x = sat (fn x' => x = x') one
(* <boxed values 58>=                           *)
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
(* <boxed values 59>=                           *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* <boxed values 60>=                           *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* <boxed values 61>=                           *)
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
(* <boxed values 62>=                           *)
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
(* <boxed values 63>=                           *)
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
(* <boxed values 64>=                           *)
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
(* <boxed values 65>=                           *)
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
(* <boxed values 66>=                           *)
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
(* <boxed values 67>=                           *)
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
(* <boxed values 68>=                           *)
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
(* <boxed values 69>=                           *)
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
(* <boxed values 70>=                           *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* <boxed values 71>=                           *)
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
(* <boxed values 72>=                           *)
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
(* <boxed values 72>=                           *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To signal an error at a given location, call *)
(* [[errorAt]].                                 *)
(* <boxed values 72>=                           *)
val _ = op errorAt : string -> srcloc -> 'a error
(* We can pair source-code locations with individual *)
(* lines and tokens. To make it easier to read the *)
(* types, I define a type abbreviation which says that a *)
(* value paired with a location is ``located.'' *)
(* <boxed values 72>=                           *)
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
(* <boxed values 73>=                           *)
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
(* <boxed values 74>=                           *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <boxed values 74>=                           *)
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
(* <boxed values 74>=                           *)
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
(* <boxed values 75>=                           *)
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
(* <boxed values 76>=                           *)
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
(* <boxed values 77>=                           *)
val _ = op <!> : 'a parser * string -> 'b parser
(* Keywords, brackets, and other literals       *)
(*                                              *)
(* It's extremely common to want to recognize literal *)
(* tokens, like the keyword [[if]] or a left or right *)
(* parenthesis. The [[literal]] parser accepts any token *)
(* whose concrete syntax is an exact match for the given *)
(* string argument.                             *)
(* <boxed values 77>=                           *)
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
(* <boxed values 78>=                           *)
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
(* <boxed values 79>=                           *)
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
(* <boxed values 80>=                           *)
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
(* <boxed values 81>=                           *)
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
(* <boxed values 82>=                           *)
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
(* <boxed values 83>=                           *)
val _ = op echoTagStream : line stream -> line stream 
(* <an interactive reader>=                     *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* Lexing and parsing with error handling       *)
(*                                              *)
(* The next step is error handling. When the code *)
(* detects an error it prints a message using function *)
(* [[errorln]].                                 *)
(* <boxed values 84>=                           *)
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
(* <boxed values 85>=                           *)
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
(* <boxed values 86>=                           *)
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
(* <boxed values 87>=                           *)
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
(* <boxed values 88>=                           *)
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
(* <boxed values 89>=                           *)
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
  (* <boxed values 91>=                           *)
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
(* Function [[letx]] forms a [[LETX]] expression, *)
(* provided there are no duplicates among the bound *)
(* names?except when the [[LETX]] expression is *)
(* [[LETSTAR]], because duplicate names in [[LETSTAR]] *)
(* are permissible.                             *)
(* <boxed values 90>=                           *)
val _ = op schemeToken : token lexer
val _ = op atom : string -> token
end


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR {\TUSCHEME}                  *)
(*                                                               *)
(*****************************************************************)

(* Abstract syntax, values, and evaluation of Typed *)
(* uScheme                                      *)
(*                                              *)
(* As with the concrete syntax, there are only minor *)
(* differences between the abstract syntax of   *)
(* micro-Scheme and the abstract syntax of Typed *)
(* uScheme. We add two new expressions, \asttylambda and *)
(* \asttyapply, which introduce and eliminate   *)
(* polymorphic types. We drop \astletrec. We also *)
(* require that the parameters of functions have *)
(* explicit types.                              *)
(* <abstract syntax and values for {\tuscheme}>= *)
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
(* The values of Typed uScheme are the same as the *)
(* values of micro-Scheme; adding a type system doesn't *)
(* require us to change any run-time representation. *)

(* The definitions of Typed uScheme are like those of *)
(* Typed Impcore, with one addition. So we can define *)
(* functions that are both recursive and polymorphic, we *)
(* provide [[VALREC]].                          *)
(* <abstract syntax and values for {\tuscheme}>= *)
datatype def = VAL    of name * exp
             | VALREC of name * tyex * exp
             | EXP    of exp
             | DEFINE of name * tyex * lambda_exp
             | USE    of name
(* In [[VALREC]], [[DEFINE]], and each parameter in *)
(* [[LAMBDA]], although the concrete syntax (page [->]) *)
(* puts the type on the left and the name on the right, *)
(* the abstract syntax puts the name on the left and the *)
(* type on the right. Why aren't they consistent? *)
(* Because the concrete syntax emulates C code and the *)
(* abstract syntax emulates common programming-language *)
(* theory.                                      *)



(*****************************************************************)
(*                                                               *)
(*   VALUES                                                      *)
(*                                                               *)
(*****************************************************************)

(* <values ((mlscheme))>=                       *)



fun embedList []     = NIL
  | embedList (h::t) = PAIR (h, embedList t)
fun embedPredicate f = fn x => BOOL (f x)
fun bool (BOOL b) = b
  | bool _        = true
(* Embedding and projection                     *)
(*                                              *)
(* An S-expression can represent an integer, Boolean, *)
(* name, function, list, etc. We may sometimes have an *)
(* ML Boolean, list, or function that we wish to *)
(* represent as an S-expression, or similarly, an *)
(* S-expression that we wish to represent as a value of *)
(* type [[bool]]. Here we define mappings between type  *)
(* [[value]] and some other ML types. Because the set of *)
(* values representable by an ML value of type [[value]] *)
(* strictly contains each of the sets of values *)
(* representable by these ML types, these mappings are *)
(* called embedding and projection. Because the *)
(* [[value]] type is strictly larger than these *)
(* ML types, no embedding operation ever fails, but a *)
(* projection operation might. [This property is a *)
(* general characteristic of any embedding/projection *)
(* pair. Mathematical terminology may clarify; an *)
(* embedding e of S into S' is an injection from S-->S'. *)
(* The corresponding projection pi_e is a left inverse *)
(* of the embedding; that is pi_e oe is the identity *)
(* function on S. There is no corresponding guarantee *)
(* for e opi_e; for example, pi_e may be undefined (_|_) *)
(* on some elements of S', or e(pi_e(x)) may not equal x *)
(* .] For example, although any ML function of type *)
(* [[value -> bool]] can be embedded into [[value]] by *)
(* using the [[PRIMITIVE]] constructor, there are values *)
(* of type [[value]] that cannot be projected into an *)
(* ML function of type [[value -> bool]].       *)
(*                                              *)
(* Lists and Booleans are straightforward. Function *)
(* [[embedPredicate]] is not a true embedding; it takes *)
(* any function returning [[bool]] and returns a *)
(* corresponding function returning [[value]]. It really *)
(* embeds the function's result, not the function *)
(* itself.                                      *)
(* <boxed values 20>=                           *)
val _ = op embedList      : value list -> value
val _ = op embedPredicate : ('a -> bool) -> ('a -> value)
val _ = op bool           : value -> bool
(* Function [[bool]] is the projection function, mapping *)
(* micro-Scheme values into ML Booleans.        *)

(* <values ((mlscheme))>=                       *)
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
(* Printing                                     *)
(*                                              *)
(* We render an S-expression as a string.       *)
(* <boxed values 21>=                           *)
val _ = op valueString : value -> string
(* The syntax [[Int.toString]] indicates the    *)
(* [[toString]] function from the standard module *)
(* [[Int]]. This function, which is part of ML's *)
(* Standard Basis Library, converts an integer to a *)
(* string. We use another standard function,    *)
(* [[String.map]], to change the minus sign from the *)
(* ML convention ([[ ]]) to the Scheme convention  *)
(* ([[-]]).                                     *)



(*****************************************************************)
(*                                                               *)
(*   TYPE CHECKING FOR {\TUSCHEME}                               *)
(*                                                               *)
(*****************************************************************)

(* <type checking for {\tuscheme}>=             *)
fun kindof (tau, Delta) =
  let (* A type variable is looked up in the environment. \ *)
      (* usetyKindIntroVar The parser guarantees that the name *)
      (* of a type variable begins with a quote mark, so it is *)
      (* distinct from any type constructor.          *)
      (* <internal function [[kind]]>=                *)
      fun kind (TYVAR a) =
            (find (a, Delta)
             handle NotFound _ => raise TypeError ("unknown type variable " ^ a)
                                                                               )
      (* A type constructor is also looked up. \usety *)
      (* KindIntroCon                                 *)
      (* <internal function [[kind]]>=                *)
        | kind (TYCON c) =
            (find (c, Delta)
             handle NotFound _ => raise TypeError ("unknown type constructor " ^
                                                                             c))
      (* The tuple type constructor may be used to combine any *)
      (* number of types. \usetyKindTuple             *)
      (* <internal function [[kind]]>=                *)
        | kind (CONAPP (TYCON "tuple", actuals)) =
            if List.all (fn tau => kind tau = TYPE) actuals then
                TYPE
            else
                raise TypeError "tuple formed from non-types"
      (* The standard function [[List.all]] corresponds to *)
      (* micro-Scheme's function [[all?]].            *)

      (* Every type constructor other than [[tuple]] must be *)
      (* applied in a way that is consistent with its kind. \ *)
      (* usetyKindApp                                 *)
      (* <internal function [[kind]]>=                *)
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
      (* A quantified type must always have kind \ktype. \ *)
      (* usetyKindAll The quantified variables \ldotsnalpha *)
      (* may be used in tau, so we insert them into Delta *)
      (* before checking the kind of tau.             *)
      (* <internal function [[kind]]>=                *)
        | kind (FORALL (alphas, tau)) =
            let val Delta' =
                  foldl (fn (a, Delta) => bind (a, TYPE, Delta)) Delta alphas
            in  case kindof (tau, Delta')
                  of TYPE    => TYPE
                   | ARROW _ => raise TypeError
                                      "quantifed a non-nullary type constructor"
            end
(* Checking a kind                              *)
(*                                              *)
(* The function [[kindof]] implements the kinding *)
(* judgment \kindistau\kind, which says that given kind *)
(* environment Delta, type-level expression tau has *)
(* kind \kind. Given Delta and tau, [[kindof(]]tau[[, ]] *)
(* Delta[[)]] returns a \kind such that \kindistau\kind, *)
(* or if no such kind exists, it raises the exception *)
(* [[TypeError]].                               *)
(* <boxed values 2>=                            *)
val _ = op kindof : tyex * kind env -> kind
val _ = op kind   : tyex            -> kind
  in  kind tau
  end
(* <type checking for {\tuscheme}>=             *)
fun asType (ty, Delta) =
  case kindof (ty, Delta)
    of TYPE    => ty
     | ARROW _ => raise TypeError ("used type constructor `" ^ typeString ty ^
                                   "' as a type")
(* A type-level expression used to describe a variable *)
(* or parameter must have kind [[TYPE]]. The function *)
(* [[asType]] ensures it.                       *)
(* <boxed values 3>=                            *)
val _ = op asType : tyex * kind env -> tyex
(* <type checking for {\tuscheme}>=             *)
fun tysubst (tau, varenv) =
  let fun subst (TYVAR a) = (find (a, varenv) handle NotFound _ => TYVAR a)
        | subst (TYCON c) = (TYCON c)
        | subst (CONAPP (tau, taus)) = CONAPP (subst tau, map subst taus)
        | subst (FORALL (alphas, tau)) =
            FORALL (alphas, tysubst (tau, bindList (alphas, map TYVAR alphas,
                                                                       varenv)))
(* The function [[tysubst (]]tau[[, varenv)]] changes *)
(* type tau by substituting for type variables as *)
(* specified by the environment [[varenv]]. Environment *)
(* [[varenv]] does not necessarily substitute for every *)
(* type variable in tau; some type variables may be left *)
(* alone. The inner function [[subst]] walks the type, *)
(* leaving [[varenv]] alone.                    *)
(* <boxed values 4>=                            *)
val _ = op tysubst : tyex * tyex env -> tyex
val _ = op subst   : tyex            -> tyex
  in  subst tau
  end
(* <type checking for {\tuscheme}>=             *)
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
(* Instantiation is a matter of substituting for type *)
(* variables. Most of the code is error checking. We *)
(* must instantiate only at type-level expressions of *)
(* kind type, we must instantiate with the right number *)
(* of types, and we must instantiate only polymorphic *)
(* types.                                       *)
(* <boxed values 5>=                            *)
val _ = op instantiate : tyex * tyex list * kind env -> tyex
val _ = List.find : ('a -> bool) -> 'a list -> 'a option
(* The standard function [[List.find]] takes a predicate *)
(* and searches a list for an element satisfying that *)
(* predicate.                                   *)

(* <type checking for {\tuscheme}>=             *)
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
(* Type equality                                *)
(*                                              *)
(* As in Typed Impcore, many rules of Typed uScheme *)
(* require that two types be the same. We can't simply *)
(* use built-in equality to check, however, because when *)
(* we compare two quantified types, the names of the *)
(* type variables should be irrelevant. For example, the *)
(* two types \/alpha\alldotlistalpha-->int and \/beta\ *)
(* alldotlistbeta-->int should be considered to be *)
(* equal. We implement the check by substituting one set *)
(* of names for the other. [*]                  *)
(* <boxed values 6>=                            *)
val _ = op eqType  : tyex      * tyex      -> bool
val _ = op eqTypes : tyex list * tyex list -> bool
(* A \xvalrec binding, by contrast, is recursive, and it *)
(* requires an explicit type. The explicit type must be *)
(* the type of the right-hand side. \tyrule ValRec \ *)
(* ptypeis[{x |->tau}] e tau \topt\xvalrec(x, tau, e) *)
(* -->Gamma{x |->tau} The bound name x is visible during *)
(* the elaboration of the right-hand side e, but for *)
(* safety, x must not be evaluated within e until after *)
(* e's value has been stored in x. In micro-Scheme, the *)
(* way to keep something from being evaluated is to *)
(* protect it under a \xlambda. [In a lazy language like *)
(* Haskell, a right-hand side is never evaluated until *)
(* its value is needed, so a definition like [[(val-rec *)
(* int x x)]] is legal, but evaluating~[[x]] produces an *)
(* infinite loop (sometimes called a ``black hole.'')] *)
(* We therefore ought to check that if [[x]] is defined *)
(* using [[val-rec]], all uses of [[x]] are protected by *)
(* \xlambdas. [This check isn't strong enough; if~you *)
(* are clever, you can find a way to subvert the type *)
(* system and force \tuscheme\ to issue the error *)
(* message ``bug in type checking.''] [*]       *)
(* <type checking for {\tuscheme}>=             *)
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
(* If you do Exercise [->], be sure to test [[not *)
(* (appearsUnprotectedIn (x, e))]] as a side condition. *)
(* For details about exactly what happens during *)
(* evaluation, see page [->] in Appendix [->].  *)

(* <type checking for {\tuscheme} ((prototype))>= *)
exception LeftAsExercise of string
fun elabdef _ = raise LeftAsExercise "elabdef"
(* Type checking                                *)
(*                                              *)
(* This book does not provide a type checker for Typed *)
(* uScheme; its implementation is left as Exercise [->]. *)
(* Type checking requires a definition, a type  *)
(* environment, and a kind environment. Calling elabdef *)
(* [[(]]t, Gamma, Delta[[)]] should return a pair (Gamma *)
(* ', s), where \toptt -->Gamma' and s is a string that *)
(* represents the type of the thing defined. [*] *)
(* <boxed values 9>=                            *)
val _ = op elabdef : def * tyex env * kind env -> tyex env * string


(*****************************************************************)
(*                                                               *)
(*   PARSING FOR {\TUSCHEME}                                     *)
(*                                                               *)
(*****************************************************************)

(* Parsing                                      *)
(*                                              *)
(* <parsing for {\tuscheme}>=                   *)
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
(* <parsing for {\tuscheme}>=                   *)
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
(* <parsing for {\tuscheme}>=                   *)
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


(* <parsing for {\tuscheme}>=                   *)
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
(* <parsing for {\tuscheme}>=                   *)
val tuschemeSyntax = (schemeToken, def)


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
(*   CHECKING AND EVALUATION FOR {\TUSCHEME}                     *)
(*                                                               *)
(*****************************************************************)

(* <checking and evaluation for {\tuscheme}>=   *)
val unitVal = NIL
(* Although in principle a value of type [[unit]] needs *)
(* no run-time representation, in our interpreter, it's *)
(* easier to provide one. The representation should be *)
(* the same everywhere because the programmer has the *)
(* right to compare two values of type [[unit]] for *)
(* equality, and our implementation of equality compares *)
(* representations. This, therefore, is a convenient *)
(* place to define a common representation:     *)
(* <boxed values 8>=                            *)
val _ = op unitVal : value
(* <checking and evaluation for {\tuscheme}>=   *)
exception BugInTypeChecking of string
(* <evaluation for {\tuscheme}>=                *)
fun eval (e, rho) =
  let fun ev (LITERAL n) = n
        (* Most of the evaluator for Typed uScheme is just like *)
        (* the evaluator for micro-Scheme in Chapter [->]. The *)
        (* code for the two new cases acts as if [[TYAPPLY]] and *)
        (* [[TYLAMBDA]] aren't there.                   *)
        (* <alternatives for [[ev]] for [[TYAPPLY]] and [[TYLAMBDA]]>= *)
        | ev (TYAPPLY  (e, _)) = ev e
        | ev (TYLAMBDA (_, e)) = ev e
        (* The rest of the evaluator appears in Appendix [->]. *)

        (* Code for variables is just as in Chapter [->]. *)
        (* <more alternatives for [[ev]] for {\tuscheme}>= *)
        | ev (VAR v) = !(find (v, rho))
        | ev (SET (n, e)) = 
            let val v = ev e
            in  find (n, rho) := v;
                v
            end
        (* Code for control flow is just as in Chapter [->]. *)
        (* <more alternatives for [[ev]] for {\tuscheme}>= *)
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
        (* Code for a [[lambda]] has to remove the types from *)
        (* the abstract syntax.                         *)
        (* <more alternatives for [[ev]] for {\tuscheme}>= *)
        | ev (LAMBDA (args, body)) = CLOSURE ((map (fn (n, ty) => n) args, body)
                                                                          , rho)
        (* Code for application is almost as in Chapter [->], *)
        (* except if the program tries to apply a non-function, *)
        (* we raise [[BugInTypeChecking]], not [[RuntimeError]], *)
        (* because the type checker should reject any program *)
        (* that could apply a non-function.             *)

        (* <more alternatives for [[ev]] for {\tuscheme}>= *)
        | ev (APPLY (f, args))  = 
               (case ev f
                  of PRIMITIVE prim => prim (map ev args)
                   | CLOSURE clo => (* <apply closure [[clo]] to [[args]] ((
                                                                 mlscheme))>= *)
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
        (* <more alternatives for [[ev]] for {\tuscheme}>= *)
        | ev (LETX (LET, bs, body)) =
            let val (names, values) = ListPair.unzip bs
            in  eval (body, bindList (names, map (ref o ev) values, rho))
            end
        | ev (LETX (LETSTAR, bs, body)) =
            let fun step ((n, e), rho) = bind (n, ref (eval (e, rho)), rho)
            in  eval (body, foldl step rho bs)
            end
(* When parsing a type, we reject anything that looks *)
(* like an expression.                          *)
(* <boxed values 13>=                           *)
val _ = op tyvar : string parser
val _ = op ty    : tyex   parser
(* Evaluation                                   *)
(*                                              *)
(* The implementation of the evaluator is almost *)
(* identical to the implementation in Chapter [->]. *)
(* There are only two significant differences: we have *)
(* to deal with the mismatch in representations between *)
(* the abstract syntax [[LAMBDA]] and the value *)
(* [[CLOSURE]], and we have to write cases for the *)
(* [[TYAPPLY]] and [[TYLAMBDA]] expressions. Another *)
(* difference is that many potential run-time errors *)
(* should be impossible because the relevant code would *)
(* be rejected by the type checker. If one of those *)
(* errors occurs anyway, we raise the exception *)
(* [[BugInTypeChecking]], not [[RuntimeError]]. *)
(* <boxed values 13>=                           *)
val _ = op eval : exp * value ref env -> value
val _ = op ev   : exp                 -> value
  in  ev e
  end
(* <evaluation for {\tuscheme}>=                *)
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
(* In the [[VALREC]] case, the interpreter evaluates  *)
(* [[e]] while [[name]] is still bound to [[NIL]]?that *)
(* is, before the assignment to [[find (name, rho)]]. *)
(* Therefore, as described on page [->], evaluating  *)
(* [[e]] must not evaluate [[name]]?because the mutable *)
(* cell for [[name]] does not yet contain its correct *)
(* value.[*]                                    *)

(* Both [[VAL]] and [[VALREC]] show names as follows: *)
(* <evaluation for {\tuscheme}>=                *)
and showVal name v =
      case v
        of CLOSURE   _ => name
         | PRIMITIVE _ => name
         | _ => valueString v
(* Evaluating a definition can produce a new    *)
(* environment. The function [[evaldef]] also returns a *)
(* string which, if nonempty, should be printed to show *)
(* the value of the item. Type soundness requires a *)
(* change in the evaluation rule for [[VAL]]; as *)
(* described in Exercise [->] in Chapter [->], [[VAL]] *)
(* must always create a new binding.            *)
(* <boxed values 14>=                           *)
val _ = op evaldef : def * value ref env -> value ref env * string
(* <evaluation for {\tuscheme}>=                *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* Primitives of Typed uScheme                  *)
(*                                              *)
(* Here are the primitives. As in Chapter [->], all are *)
(* either binary or unary operators. Type checking *)
(* should guarantee that operators are used with the *)
(* correct arity.                               *)
(* <boxed values 15>=                           *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* <evaluation for {\tuscheme}>=                *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
val arithtype = funtype ([inttype, inttype], inttype)
(* Arithmetic primitives expect and return integers. *)
(* <boxed values 16>=                           *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
val _ = op arithtype : tyex
(* As in Chapter [->], we use the chunk [[<<primitive *)
(* functions for Typed uScheme [[::]]>>]] to cons up all *)
(* the primitives into one giant list, and we use that *)
(* list to build the initial environment for the *)
(* read-eval-print loop. The big difference is that in *)
(* Typed uScheme, each primitive has a type as well as a *)
(* value.                                       *)

(* <evaluation for {\tuscheme}>=                *)
fun embedPredicate f args = BOOL (f args)
fun comparison f = binaryOp (embedPredicate f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")
val comptype = funtype ([inttype, inttype], booltype)
(* Comparisons take two arguments. Most comparisons *)
(* (except for equality) apply only to integers. *)
(* <boxed values 17>=                           *)
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
(* Processing definitions in two phases         *)
(*                                              *)
(* As in Typed Impcore, we process a definition by first *)
(* elaborating it (which includes running the type *)
(* checker), then evaluating it. The elaborator produces *)
(* a string that represents a type, and the evaluator *)
(* produces a string that either is empty or represents *)
(* a value. If the value string is nonempty, we print *)
(* both strings.                                *)
(* <boxed values 10>=                           *)
val _ = op checkThenEval : def * env_bundle * (string->unit) -> env_bundle
        in  (delta, gamma, rho)
        end
(* <checking and evaluation for {\tuscheme}>=   *)
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
(* The read-eval-print loop is exactly as for Typed *)
(* Impcore.                                     *)
(* <boxed values 11>=                           *)
val _ = op readCheckEvalPrint : def stream * (string->unit) * (string->unit) ->
                                                        env_bundle -> env_bundle
(* We have the same new handlers as in Typed Impcore. *)



(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION FOR {\TUSCHEME}                              *)
(*                                                               *)
(*****************************************************************)

(* <initialization for {\tuscheme}>=            *)
val initialEnvs =
  let fun addPrim ((name, prim, funty), (types, values)) = 
        ( bind (name, funty, types)
        , bind (name, ref (PRIMITIVE prim), values)
        )
      val (types, values) = foldl addPrim (emptyEnv, emptyEnv)
                            ((* <primitive functions for {\tuscheme}\ [[::]]>=
                                                                              *)
                             ("+", arithOp op +,   arithtype) :: 
                             ("-", arithOp op -,   arithtype) :: 
                             ("*", arithOp op *,   arithtype) :: 
                             ("/", arithOp op div, arithtype) ::
                             (* <primitive functions for {\tuscheme}\ [[::]]>=
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
                             (* The list primitives have polymorphic types.  *)
                             (* <primitive functions for {\tuscheme}\ [[::]]>=
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
                             (* The [[print]] primitive also has a polymorphic
                                                                        type. *)
                             (* <primitive functions for {\tuscheme}\ [[::]]>=
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
                            ((* In plain Typed uScheme, all the primitives are
                                                                              *)
                             (* functions, so this chunk is empty. But you might
                                                                          add *)
                             (* to it in the Exercises.                      *)
                             (* <primitives that aren't functions, for {\
                                                          tuscheme}\ [[::]]>= *)
                             (* if this space is completely empty, something
                                       goes wrong with the software OMIT *) nil)
      fun addKind ((name, kind), kinds) = bind (name, kind, kinds)
      val kinds   = foldl addKind emptyEnv
                    ((* How do we know which type constructors have which *)
                     (* kinds? In Typed Impcore, we consult type rules. For *)
                     (* example, the \rulenameBaseTypes rule shows that *)
                     (* [[int]] has kind \ktype, and the \rulename   *)
                     (* ArrayFormation rule shows that [[array]] has kind \ *)
                     (* ktype\karrow\ktype. But one of the problems we are *)
                     (* trying to solve is that type rules are not easily *)
                     (* extensible. In Typed uScheme, type constructors are *)
                     (* not built in. Instead, we put the kind of each *)
                     (* constructor in a kind environment. Here is an example *)
                     (* environment that shows common type constructors and *)
                     (* their kinds. For clarity, we write the binding in a *)
                     (* kind environment using the :: symbol instead of |->. *)
                     (* (As noted above, the :: symbol is pronounced *)
                     (* ``has kind.'')                               *)
                     (*                                              *)
                     (*  Delta_0 int:: \ktype, bool:: \ktype, unit:: \ *)
                     (*  = {     ktype, pair :: \ktype*\ktype\karrow\ktype *)
                     (*          ,                                   *)
                     (*          sum :: \ktype*\ktype\karrow\ktype, --> :: *)
                     (*          \ktype*\ktype\karrow\ktype, array :: \ *)
                     (*          ktype\karrow\ktype, list :: \ktype\karrow *)
                     (*          \ktype }                            *)
                     (*                                              *)
                     (* All by itself, this environment enables us to see how *)
                     (* both [[int]] and [[array]] may be used. Even better, *)
                     (* we can add new type constructors to a language just *)
                     (* by adding them to the kind environment. Here are the *)
                     (* type constructors that are built into Typed uScheme, *)
                     (* except those that are left as Exercises.     *)
                     (* <primitive type constructors for {\tuscheme}\ [[::]]>=
                                                                              *)
                     ("int",      TYPE) ::
                     ("bool",     TYPE) ::
                     ("sym",      TYPE) ::
                     ("unit",     TYPE) ::
                     ("list",     ARROW ([TYPE],       TYPE)) ::
                     ("function", ARROW ([TYPE, TYPE], TYPE)) ::
                     (* As these examples show, kinds classify types in much *)
                     (* the same way that types classify expressions. *)
 nil)
      val envs    = (kinds, types, values)
      val basis   = (* Further reading                              *)
                    (*                                              *)
                    (* \citetkoenig:anecdote describes an experience with *)
                    (* ML type inference which leads to a conclusion that *)
                    (* resembles my conclusion about the type of    *)
                    (* [[noneIfLineEnds]] on page [->].             *)
                    (*                                              *)
                    (* <ML representation of initial basis>=        *)

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
(* Initializing the interpreter                 *)
(*                                              *)
(* To put everything together into a working    *)
(* interpreter, we need an initial kind environment as *)
(* well as a type environment and a value environment. *)
(* <boxed values 12>=                           *)
val _ = op kinds  : kind      env
val _ = op types  : tyex      env
val _ = op values : value ref env
val _ = op envs   : env_bundle
      val defs  = reader tuschemeSyntax noPrompts ("initial basis", streamOfList
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
(* <initialization for {\tuscheme}>=            *)
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
