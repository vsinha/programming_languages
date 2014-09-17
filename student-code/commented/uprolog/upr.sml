(* Putting the pieces together                  *)
(*                                              *)
(* We stitch together the parts of the implementation in *)
(* this order:                                  *)
(* <upr.sml>=                                   *)


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
(* <boxed values 11>=                           *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* Because ML strings are immutable, we can use them to *)
(* represent names directly. We also use exceptions, not *)
(* an [[error]] procedure, to indicate when things have *)
(* gone wrong. The exceptions we use are listed in *)
(* Table [->].                                  *)

(* Tracing code is helpful for debugging.       *)
(* <environments>=                              *)
val tracer = ref (app print)
val _ = tracer := (fn _ => ())
fun trace l = !tracer l
(* Complete implementation of uProlog           *)
(*                                              *)
(* Substitution                                 *)
(*                                              *)



(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* Abstract syntax (and no values)              *)
(*                                              *)
(* Of all the languages in this book, Prolog has the *)
(* simplest structure. Unusually, there is no   *)
(* distinction between ``values'' and ``abstract syntax; *)
(* '' both are represented as terms. A term is a *)
(* variable, a literal constant, or an application of a *)
(* functor to a list of terms. [Functors play the same *)
(* role in \prolog\ that datatype constructors play in~\ *)
(* ml, including participation in pattern matching.] The *)
(* only kinds of literal constants in uProlog are *)
(* integers.                                    *)
(* <abstract syntax and values ((upr))>=        *)
datatype term = VAR     of string
              | LITERAL of int
              | APPLY   of string * term list
(* Goals and applications have identical structure. *)
(* A term can be a functor applied to a list of terms; a *)
(* goal is a predicate applied to a list of terms. A *)
(* ``functor'' or a ``predicate'' is uniquely identified *)
(* by its name.                                 *)
(* <abstract syntax and values ((upr))>=        *)
type goal = string * term list
(* <abstract syntax and values ((upr))>=        *)
datatype clause = :- of goal * goal list
infix 3 :-
(* At the top level, we can do three things: add a *)
(* clause to the database, ask a query, or include a *)
(* file. The switch back and forth between query mode *)
(* and rule mode is hidden from the code in this *)
(* chapter; the details are buried in Section [->]. *)
(* In other interpreters, the thing that appears at top *)
(* level is a ``definition;'' because Prolog has no *)
(* definitions, we call the top-level syntactic *)
(* category [[cq]], which is short for clause-or-query.  *)
(* [*]                                          *)
(* <abstract syntax and values ((upr))>=        *)
datatype cq
  = ADD_CLAUSE of clause
  | QUERY      of goal list
  | USE        of string
(* <abstract syntax and values ((upr))>=        *)
(* <string conversions ((upr))>=                *)
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
(* <string conversions ((upr))>=                *)
fun goalString g = termString (APPLY g)
fun clauseString (g :- []) = goalString g
  | clauseString (g :- (h :: t)) =
      String.concat (goalString g :: " :- " :: goalString h ::
                     (foldr (fn (g, tail) => ", " :: goalString g :: tail)) [] t
                                                                               )
(* There is no ``evaluation.'' [Well, hardly any. The *)
(* primitive [[is]] does a tiny amount of evaluation.] *)
(* Instead, we have queries. The main features of the *)
(* implementation are the database, substitution and *)
(* unification (which are left as Exercises [->] and  *)
(* [->]), and the backtracking query engine. To print *)
(* queries and answers, we use code from Appendix [->]. *)
(* <boxed values 1>=                            *)
val _ = op termString   : term   -> string
val _ = op goalString   : goal   -> string
val _ = op clauseString : clause -> string


(*****************************************************************)
(*                                                               *)
(*   CLAUSE DATABASE                                             *)
(*                                                               *)
(*****************************************************************)

(* <clause database>=                           *)
type database = clause list
val emptyDatabase = []
fun addClause (r, rs) = rs @ [r] (* must maintain order *)
fun potentialMatches (_, rs) = rs


(*****************************************************************)
(*                                                               *)
(*   SUBSTITUTION AND UNIFICATION                                *)
(*                                                               *)
(*****************************************************************)

(* <substitution and unification ((upr))>=      *)
(* <substitution on terms ((prototype))>=       *)
exception LeftAsExercise
type subst = term -> term
infix 7 |-->
fun name |--> term = raise LeftAsExercise
fun idsubst term = term
(* Our implementation uses a simple list. We treat every *)
(* clause as a potential match.                 *)
(* <boxed values 2>=                            *)
type database = database
val _ = op emptyDatabase    : database
val _ = op addClause        : clause * database -> database
val _ = op potentialMatches : goal * database -> clause list
(* Substitution                                 *)
(*                                              *)
(* A substitution \subsn is a function from terms to *)
(* terms. We present only prototype code for    *)
(* substitutions; the full implementation is left as *)
(* Exercise [->].                               *)
(* <boxed values 2>=                            *)
type subst = subst
val _ = op idsubst : subst
val _ = op |-->    : name * term -> subst
(* [*]                                          *)

(* Given the ability to substitute in a term, we may *)
(* also want to substitute in goals and clauses. Using *)
(* the notation of Section [->], if [[theta]]   *)
(* represents \subsn, then [[lift theta]] represents \ *)
(* widehat\subsn.                               *)

(* <substitution and unification ((upr))>=      *)
fun lift       theta (f, l)    = (f, map theta l)
fun liftClause theta (c :- ps) = (lift theta c :- map (lift theta) ps)
(* <boxed values 3>=                            *)
val _ = op lift       : subst -> (goal   -> goal)
val _ = op liftClause : subst -> (clause -> clause)
(* <substitution and unification ((upr))>=      *)
type 'a set = 'a list
val emptyset = []
fun member x = 
  List.exists (fn y => y = x)
fun insert (x, l) = 
  if member x l then l else x::l
fun diff  (s1, s2) = 
  List.filter (fn x => not (member x s2)) s1
fun union (s1, s2) = s1 @ diff (s2, s1)   (* preserves order *)
(* Sets of variables                            *)
(*                                              *)
(* As in Chapter [->], we use sets of variables in *)
(* unification. We provide a simple implementation using *)
(* lists. The double prime in the type variable [[''a]] *)
(* means that [[''a]] has to be an ``equality type,'' *)
(* i.e., variable [[''a]] may be instantiated only at *)
(* types that admit equality.                   *)
(* <boxed values 4>=                            *)
type 'a set = 'a set
val _ = op emptyset : 'a set
val _ = op member   : ''a -> ''a set -> bool
val _ = op insert   : ''a     * ''a set  -> ''a set
val _ = op union    : ''a set * ''a set  -> ''a set
val _ = op diff     : ''a set * ''a set  -> ''a set
(* <substitution and unification ((upr))>=      *)
fun freevars t =
  let fun f(VAR v,     l) = insert (v, l)
        | f(LITERAL _, l) = l
        | f(APPLY(_, args), l) = foldl f l args
  in  rev (f(t, []))
  end  
fun freevarsGoal goal = freevars (APPLY goal)
fun freevarsClause (c :- ps) =
  foldl (fn (p, f) => union (freevarsGoal p, f)) (freevarsGoal c) ps
(* The function [[freevars]] computes the free variables *)
(* of a term. For readability, we ensure that variables *)
(* appear in the set in the order of their first *)
(* appearance in the type, when reading from left to *)
(* right. We provide similar functions on goals and *)
(* clauses.                                     *)
(* <boxed values 5>=                            *)
val _ = op freevars       : term   -> name set
val _ = op freevarsGoal   : goal   -> name set
val _ = op freevarsClause : clause -> name set
(* <substitution and unification ((upr))>=      *)
local
  val n = ref 1
in
  fun freshVar s = VAR ("_" ^ s ^ Int.toString (!n) before n := !n + 1)
(* ``Freshening''                               *)
(*                                              *)
(* Every time we use a clause, the semantics of Prolog *)
(* require that we rename its variables to fresh *)
(* variables. To rename a variable, we put an underscore *)
(* in front of its name and a unique integer after it. *)
(* Because the parser in Section [->] does not accept *)
(* variables whose names begin with an underscore, these *)
(* names cannot possibly collide with the names of *)
(* variables written by users.                  *)
(* <boxed values 6>=                            *)
val _ = op freshVar : string -> term
end
(* <substitution and unification ((upr))>=      *)
fun freshen c =
  let val free     = freevarsClause c
      val fresh    = map freshVar free
      val renaming =
        ListPair.foldl (fn (free, fresh, theta) => theta o (free |--> fresh))
        idsubst (free, fresh) 
  in  liftClause renaming c
  end
(* <substitution and unification ((upr))>=      *)
(* <unification ((prototype))>=                 *)
exception Unify
fun unifyTerm (t1, t2) = 
  raise LeftAsExercise
and unifyList (ts1, ts2) = 
  raise LeftAsExercise
fun unify ((f, args), (f', args')) =
  if f = f' then unifyList (args, args') else raise Unify
(* Function [[freshen]] replaces free variables with *)
(* fresh variables. Value [[renaming]] represents a *)
(* renaming \renaming, as in Section [->].      *)
(* <boxed values 7>=                            *)
val _ = op freshen : clause -> clause
(* Unification                                  *)
(*                                              *)
(* Given goals g and G, unify(g, G) returns a   *)
(* substitution \subsn such that \wh\subsn(g)=\wh\subsn *)
(* (G), or if no such substitution exists, it raises *)
(* [[Unify]]. The implementation of unification is left *)
(* as Exercise [->]. [*]                        *)
(* <boxed values 7>=                            *)
val _ = op unify     : goal      * goal      -> subst
val _ = op unifyTerm : term      * term      -> subst
val _ = op unifyList : term list * term list -> subst


(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS                                            *)
(*                                                               *)
(*****************************************************************)

(* <lexical analysis ((upr))>=                  *)
datatype token 
  = UPPER     of string
  | LOWER     of string
  | SYMBOLIC  of string
  | INT_TOKEN of int
  | RESERVED  of string
  | EOF
(* Lexical analysis                             *)
(*                                              *)
(* Tokens                                       *)
(*                                              *)
(* uProlog has a more complex lexical structure than *)
(* other languages. We have uppercase, lowercase, and *)
(* symbolic tokens, as well as integers. It simplifies *)
(* the parser if we distinguish reserved words and *)
(* symbols using [[RESERVED]]. Finally, because a *)
(* C-style uProlog comment can span multiple lines, *)
(* we have to be prepared for the lexical analyzer to *)
(* encounter end-of-file. Reading end of file needs to *)
(* be distinguishable from failing to read a token, so *)
(* I represent end of file by its own special token  *)
(* [[EOF]].                                     *)
(* <boxed values 91>=                           *)
type token = token
(* We need to print tokens in error messages.   *)
(* <lexical analysis ((upr))>=                  *)
fun tokenString (UPPER s)     = s
  | tokenString (LOWER s)     = s
  | tokenString (INT_TOKEN n) = if n < 0 then "-" ^ Int.toString (~n)
                                else Int.toString n
  | tokenString (SYMBOLIC  s) = s
  | tokenString (RESERVED  s) = s
  | tokenString EOF           = "<end-of-file>"
(* We need to identify literals for the parser. The *)
(* treatment of integer literals is a bit dodgy, but *)
(* they shouldn't be used for parsing.          *)
(* <lexical analysis ((upr))>=                  *)
fun isLiteral s t = (s = tokenString t)
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
(* <boxed values 22>=                           *)
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
(* <boxed values 23>=                           *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a streams is read, no new actions are performed. *)
(* <boxed values 23>=                           *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* <boxed values 24>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such stream, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 24>=                           *)
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
(* <boxed values 25>=                           *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* <streams>=                                   *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 26>=                           *)
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
(* <boxed values 27>=                           *)
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
(* <boxed values 28>=                           *)
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
(* <boxed values 29>=                           *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* <boxed values 29>=                           *)
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
(* <boxed values 30>=                           *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 31>=                           *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right: [*]                                   *)
(* <boxed values 32>=                           *)
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
(* <boxed values 33>=                           *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 33>=                           *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 34>=                           *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 35>=                           *)
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
(* <boxed values 36>=                           *)
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
(* <boxed values 37>=                           *)
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
(* <boxed values 38>=                           *)
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
(* <boxed values 38>=                           *)
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
(* <boxed values 39>=                           *)
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
(* <boxed values 40>=                           *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* has a special operator [[<>]], which is also *)
(* pronounced ``applied to.'' It combines a B-to-C *)
(* function with an \atob transformer to produce an \ *)
(* atoc transformer.                            *)
(* <boxed values 41>=                           *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* <boxed values 42>=                           *)
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
(* <boxed values 43>=                           *)
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
(* <boxed values 44>=                           *)
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
(* <boxed values 45>=                           *)
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
(* <boxed values 46>=                           *)
val _ = op eos : ('a, unit) xformer
(* <parsing combinators>=                       *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* It can also be useful to peek at the contents of a *)
(* stream, without looking at any input, and while *)
(* ignoring errors.                             *)
(* <boxed values 47>=                           *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* <parsing combinators>=                       *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* And we might want to transform some input, then *)
(* rewind it back to the starting point. (Actions can't *)
(* be undone, but at least the input can be read again.) *)
(* <boxed values 48>=                           *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* <boxed values 49>=                           *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun oneEq x = sat (fn x' => x = x') one
(* <boxed values 50>=                           *)
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
(* <boxed values 51>=                           *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* <boxed values 52>=                           *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* <boxed values 53>=                           *)
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
(* <boxed values 54>=                           *)
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
(* <boxed values 55>=                           *)
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
(* <boxed values 56>=                           *)
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
(* <boxed values 57>=                           *)
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
(* <boxed values 58>=                           *)
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
(* <boxed values 59>=                           *)
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
(* <boxed values 60>=                           *)
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
(* <boxed values 61>=                           *)
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
(* <boxed values 62>=                           *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* <boxed values 63>=                           *)
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
(* <boxed values 64>=                           *)
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
(* <boxed values 64>=                           *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To signal an error at a given location, call *)
(* [[errorAt]].                                 *)
(* <boxed values 64>=                           *)
val _ = op errorAt : string -> srcloc -> 'a error
(* We can pair source-code locations with individual *)
(* lines and tokens. To make it easier to read the *)
(* types, I define a type abbreviation which says that a *)
(* value paired with a location is ``located.'' *)
(* <boxed values 64>=                           *)
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
(* <boxed values 65>=                           *)
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
(* <boxed values 66>=                           *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <boxed values 66>=                           *)
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
(* <boxed values 66>=                           *)
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
(* <boxed values 67>=                           *)
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
(* <boxed values 68>=                           *)
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
(* <boxed values 69>=                           *)
val _ = op <!> : 'a parser * string -> 'b parser
(* Keywords, brackets, and other literals       *)
(*                                              *)
(* It's extremely common to want to recognize literal *)
(* tokens, like the keyword [[if]] or a left or right *)
(* parenthesis. The [[literal]] parser accepts any token *)
(* whose concrete syntax is an exact match for the given *)
(* string argument.                             *)
(* <boxed values 69>=                           *)
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
(* <boxed values 70>=                           *)
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
(* <boxed values 71>=                           *)
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
(* <boxed values 72>=                           *)
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
(* <boxed values 73>=                           *)
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
(* <boxed values 74>=                           *)
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
(* <boxed values 75>=                           *)
val _ = op echoTagStream : line stream -> line stream 
(* <an interactive reader>=                     *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* Lexing and parsing with error handling       *)
(*                                              *)
(* The next step is error handling. When the code *)
(* detects an error it prints a message using function *)
(* [[errorln]].                                 *)
(* <boxed values 76>=                           *)
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
(* <boxed values 77>=                           *)
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
(* <boxed values 78>=                           *)
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
(* <boxed values 79>=                           *)
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
(* <boxed values 80>=                           *)
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
(* <boxed values 81>=                           *)
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

(* Reserved words and anonymous variables       *)
(*                                              *)
(* Tokens formed from symbols or from lower-case letters *)
(* are usually symbolic, but sometimes they are reserved *)
(* words. And because the cut is nullary, not binary, it *)
(* is treated as an ordinary symbol, just like any other *)
(* nullary predicate.                           *)
(* <lexical analysis ((upr))>=                  *)
fun symbolic ":-" = RESERVED ":-"
  | symbolic "."  = RESERVED "."
  | symbolic "|"  = RESERVED "|"
  | symbolic "!"  = LOWER "!"
  | symbolic s    = SYMBOLIC s
fun lower "is" = RESERVED "is"
  | lower s    = LOWER s
(* A variable consisting of a single underscore gets *)
(* converted to a unique ``anonymous'' variable. *)
(* <lexical analysis ((upr))>=                  *)
fun anonymousVar () =
  case freshVar ""
    of VAR v => UPPER v
     | _ => let exception ThisCan'tHappen in raise ThisCan'tHappen end
(* <lexical analysis ((upr))>=                  *)
local
  (* Classification of characters                 *)
  (*                                              *)
  (* The other languages in this book treat only  *)
  (* parentheses, digits, and semicolons specially. But in *)
  (* Prolog, we distinguish two kinds of names: symbolic *)
  (* and alphanumeric. A symbolic name like [[+]] is used *)
  (* differently from an alphanumeric name like [[add1]]. *)
  (* This difference is founded on a different    *)
  (* classification of characters. In uProlog, every *)
  (* character is either a symbol, an alphanumeric, a *)
  (* space, or a delimiter.                       *)
  (* <character-classification functions for \uprolog>= *)
  val symbols = explode "!%^&*-+:=|~<>/?`$\\"
  fun isSymbol c = List.exists (fn c' => c' = c) symbols
  fun isIdent  c = Char.isAlphaNum c orelse c = #"_"
  fun isDelim  c = not (isIdent c orelse isSymbol c)
  (* <lexical utility functions for \uprolog>=    *)
  fun underscore _ [] = OK (anonymousVar ())
    | underscore c cs = ERROR ("name may not begin with underscore at " ^
                                   implode (c::cs))

  fun int cs [] = intFromChars cs >>=+ INT_TOKEN
    | int cs ids = 
        ERROR ("integer literal " ^ implode cs ^
               " may not be followed by '" ^ implode ids ^ "'")
  (* Utility functions [[underscore]] and [[int]] make *)
  (* sure that an underscore or a sequence of digits, *)
  (* respectively, is never followed by any character that *)
  (* might be part of an alphanumeric identifier. When *)
  (* either of these functions succeeds, it returns an *)
  (* appropriate token.                           *)
  (* <boxed values 92>=                           *)
  val _ = op underscore : char      -> char list -> token error
  val _ = op int        : char list -> char list -> token error
  (* <lexical utility functions for \uprolog>=    *)
  fun unrecognized (ERROR _) = let exception Can'tHappen in raise Can'tHappen
                                                                             end
    | unrecognized (OK cs) =
        case cs
          of []        => NONE
           | #";" :: _ => let exception Can'tHappen in raise Can'tHappen end
           | _ =>
               SOME (ERROR ("invalid initial character in `" ^ implode cs ^ "'")
                                                                          , EOS)
  (* Utility function [[unrecognized]] is called when the *)
  (* lexical analyzer cannot recognize a sequence of *)
  (* characters. If the sequence is empty, it means *)
  (* there's no token. If anything else happens, an error *)
  (* has occurred.                                *)
  (* <boxed values 93>=                           *)
  val _ = op unrecognized : char list error -> ('a error * 'a error stream)
                                                                          option
  (* <lexical utility functions for \uprolog>=    *)
  fun nextline (file, line) = (file, line+1)
  (* When a lexical analyzer runs out of characters on a *)
  (* line, it calls [[nextline]] to compute the location *)
  (* of the next line.                            *)
  (* <boxed values 94>=                           *)
  val _ = op nextline : srcloc -> srcloc
in
  (* <lexical analyzers for for \uprolog>=        *)
  type 'a prolog_lexer = (char inline, 'a) xformer
  fun char chars =
    case streamGet chars
      of SOME (INLINE c, chars) => SOME (OK c, chars) 
       | _ => NONE
  fun eol chars =
    case streamGet chars
      of SOME (EOL _, chars) => SOME (OK (), chars)
       | _ => NONE
  (* <lexical analyzers for for \uprolog>=        *)
  fun charEq c =
    sat (fn c' => c = c') char
  fun manySat p =
    many (sat p char)

  val whitespace =
    manySat Char.isSpace
  val intChars = 
    (curry op :: <$> charEq #"-" <|> pure id) <*> many1 (sat Char.isDigit char)
  (* <boxed values 95>=                           *)
  type 'a prolog_lexer = 'a prolog_lexer
  val _ = op char : char prolog_lexer
  val _ = op eol  : unit prolog_lexer
  (* uProlog must be aware of the end of an input line. *)
  (* Lexical analyzers [[char]] and [[eol]] recognize a *)
  (* character and the end-of-line marker, respectively. *)

  (* Functions [[charEq]] and [[manySat]] provide general *)
  (* tools for recognizing characters and sequences of *)
  (* characters. Lexers [[whitespace]] and [[intChars]] *)
  (* handle two common cases.                     *)
  (* <boxed values 95>=                           *)
  val _ = op charEq     : char -> char prolog_lexer
  val _ = op manySat    : (char -> bool) -> char list prolog_lexer
  val _ = op whitespace : char list prolog_lexer
  val _ = op intChars   : char list prolog_lexer
  (* <lexical analyzers for for \uprolog>=        *)
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
  (* <lexical analyzers for for \uprolog>=        *)
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
  (* An ordinary token is an underscore, delimiter, *)
  (* integer literal, symbolic name, or alphanumeric name. *)
  (* Uppercase and lowercase names produce different *)
  (* tokens.                                      *)
  (* <boxed values 96>=                           *)
  val _ = op ordinaryToken : token prolog_lexer
  (* We need two main lexical analyzers that keep track of *)
  (* source locations: [[tokenAt]] produces tokens, and *)
  (* [[skipComment]] skips comments. They are mutually *)
  (* recursive, and in order to delay the recursive calls *)
  (* until a stream is supplied, each definition has an *)
  (* explicit [[cs]] argument, which contains a stream of *)
  (* inline characters.                           *)
  (* <boxed values 96>=                           *)
  val _ = op tokenAt     : srcloc -> token located prolog_lexer
  val _ = op skipComment : srcloc -> srcloc -> token located prolog_lexer
end


(*****************************************************************)
(*                                                               *)
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* <parsing ((upr))>=                           *)
val symbol = (fn SYMBOLIC  s => SOME s | _ => NONE) <$>? token
val upper  = (fn UPPER     s => SOME s | _ => NONE) <$>? token
val lower  = (fn LOWER     s => SOME s | _ => NONE) <$>? token
val int    = (fn INT_TOKEN n => SOME n | _ => NONE) <$>? token
(* Parsing                                      *)
(*                                              *)
(* [*]                                          *)
(*                                              *)
(* Utilities for parsing uProlog                *)
(*                                              *)
(* <boxed values 97>=                           *)
val _ = op symbol : string parser
val _ = op upper  : string parser
val _ = op lower  : string parser
val _ = op int    : int    parser
(* <parsing ((upr))>=                           *)
val notSymbol =
  symbol <!> "arithmetic expressions must be parenthesized" <|>
  pure ()
(* We use these combinators to define the grammar from *)
(* Figure [->]. We use [[notSymbol]] to ensure that a *)
(* term like [[3 + X]] is not followed by another *)
(* symbol. This means we don't parse such terms as [[3 + *)
(* X + Y]].                                     *)
(* <boxed values 98>=                           *)
val _ = op notSymbol : unit parser
(* <parsing ((upr))>=                           *)
fun nilt tokens = pure (APPLY ("nil", [])) tokens
fun cons (x, xs) = APPLY ("cons", [x, xs])
(* Parser [[nilt]] uses the empty list of tokens to *)
(* represent the empty list of terms. It needs an *)
(* explicit type constraint to avoid falling afoul of *)
(* the value restriction on polymorphism. Function *)
(* [[cons]] combines two terms, which is useful for *)
(* parsing lists.                               *)
(* <boxed values 99>=                           *)
val _ = op nilt : term parser
val _ = op cons : term * term -> term
(* <parsing ((upr))>=                           *)
val variable        = upper
val binaryPredicate = symbol
val functr          = lower
fun commas p = 
  curry op :: <$> p <*> many ("," >-- p)
(* Here is one utility function [[commas]], plus *)
(* renamings of three other functions.          *)
(* <boxed values 100>=                          *)
val _ = op variable        : string parser
val _ = op binaryPredicate : string parser
val _ = op functr          : string parser
val _ = op commas : 'a parser -> 'a list parser
(* I have to spell ``functor'' without the ``o'' because *)
(* in Standard ML, [[functor]] is a reserved word. *)

(* <parsing ((upr))>=                           *)
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
(* Parsing terms, atoms, and goals              *)
(*                                              *)
(* We're now ready to parse uProlog. The grammar is *)
(* based on the grammar from \figrefpageprolog.syntax, *)
(* except that I'm using named function to parse atoms, *)
(* and I use some specialized tricks to organize the *)
(* grammar. Concrete syntax is not for the faint of *)
(* heart.                                       *)
(* <boxed values 101>=                          *)
val _ = op term   : term parser
val _ = op atom   : term parser
val _ = op commas : 'a parser -> 'a list parser
(* <parsing ((upr))>=                           *)
fun asGoal _   (APPLY g) = OK g
  | asGoal loc (VAR v)   = 
      errorAt ("Variable " ^ v ^ " cannot be a predicate") loc
  | asGoal loc (LITERAL n) =
      errorAt ("Integer " ^ Int.toString n ^ " cannot be a predicate") loc

val goal = asGoal <$> srcloc <*>! term 
(* <boxed values 102>=                          *)
val _ = op asGoal : srcloc -> term -> goal error
val _ = op goal   : goal parser
(* <parsing ((upr))>=                           *)
datatype concrete
  = BRACKET of string 
  | CLAUSE  of goal * goal list option
  | GOALS   of goal list

val notClosing = sat (fn RESERVED "]" => false | _ => true) token

val concrete = 
     (BRACKET o concat o map tokenString) <$> "[" >-- many notClosing --< "]"
 <|> curry CLAUSE <$> goal <*> ":-" >-- (SOME <$> commas goal)
 <|> GOALS <$> commas goal
(* Recognizing concrete syntax using modes      *)
(*                                              *)
(* I put together the uProlog parser in three layers. *)
(* The bottom layer is the concrete syntax itself. For a *)
(* moment let's ignore the meaning of uProlog's syntax *)
(* and look only at what can appear. At top level, we *)
(* might see                                    *)
(*                                              *)
(*   * A string in brackets                     *)
(*   * A clause containing a [[:-]] symbol      *)
(*   * A list of one or more goals separated by commas *)
(*                                              *)
(* <boxed values 103>=                          *)
type concrete = concrete
val _ = op concrete : concrete parser
(* <parsing ((upr))>=                           *)
datatype mode = QMODE | RMODE

fun mprompt RMODE = "-> "
  | mprompt QMODE = "?- "
(* [*] In most cases, we know what these things are *)
(* supposed to mean, but there's one case in which we *)
(* don't: a phrase like ``[[color(yellow).]]'' could be *)
(* either a clause or a query. To know which is meant, *)
(* we have to know the mode. In other words, the mode *)
(* distinguishes [[CLAUSE(g, NONE)]] from [[GOALS [g]]]. *)
(* A parser may be in either query mode or rule (clause) *)
(* mode, and each mode has its own prompt.      *)
(* <boxed values 104>=                          *)
type mode = mode
val _ = op mprompt : mode -> string
(* <parsing ((upr))>=                           *)
datatype cq_or_mode
  = CQ of cq
  | NEW_MODE of mode
(* The concrete syntax normally means a clause or query, *)
(* which is denoted by the syntactic nonterminal symbol *)
(* clause-or-query and represented by an ML value of *)
(* type [[cq]] (see chunk [->] in \chaprefprolog). But *)
(* particular concrete syntax, such as ``[[[rule].]]'' *)
(* or ``[[[query].]],'' can be an instruction to change *)
(* to a new mode. The middle layer of uProlog's parser *)
(* produces a value of type [[cq_or_mode]], which is *)
(* defined as follows:                          *)
(* <boxed values 105>=                          *)
type cq_or_mode = cq_or_mode
(* <parsing ((upr))>=                           *)
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
(* The next level of uProlog's parser interpreters a *)
(* [[concrete]] value according to the mode. All  *)
(* [[BRACKET]] values are interpreted in the same way *)
(* regardless of mode, but clauses and especially *)
(* [[GOALS]] are interpreted differently in rule mode *)
(* and in query mode.                           *)
(* <boxed values 106>=                          *)
val _ = op interpretConcrete : mode -> concrete -> cq_or_mode error
(* <parsing ((upr))>=                           *)
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
(* Parser [[cq_or_mode]] m parses a [[concrete]] *)
(* according to mode m. If it sees something it doesn't *)
(* recognize, it emits an error message and skips ahead *)
(* until it sees a dot or the end of the input. *)
(* Importantly, this parser never fails: it always *)
(* returns either a [[cq_or_mode]] value or an error *)
(* message.                                     *)
(* <boxed values 107>=                          *)
val _ = op cq_or_mode : mode -> cq_or_mode parser
(* <parsing ((upr))>=                           *)
fun prologReader noisy initialMode (name, lines) =
  let val (ps1, ps2) = (mprompt initialMode, "   ")
      val thePrompt = ref ""  (* no prompt unless noisy *)
      val setPrompt = if noisy then (fn s => thePrompt := s) else (fn _ => ())

      type read_state = string * mode * token located inline stream
      (* <utility functions for [[prologReader]]>=    *)
      fun startsWithEOF tokens =
        case streamGet tokens
          of SOME (INLINE (_, EOF), _) => true
           | _ => false
      (* Function [[getCq]] uses [[startsWithEOF]] to check if *)
      (* the input stream has no more tokens.         *)
      (* <boxed values 109>=                          *)
      val _ = op startsWithEOF : token located inline stream -> bool
      (* <utility functions for [[prologReader]]>=    *)
      fun skipPastDot tokens =
        case streamGet tokens
          of SOME (INLINE (_, RESERVED "."), tokens) => tokens
           | SOME (INLINE (_, EOF), tokens) => tokens
           | SOME (_, tokens) => skipPastDot tokens
           | NONE => tokens
      (* If [[getCq]] detects an error, it skips tokens in the *)
      (* input up to and including the next dot.      *)
      (* <boxed values 110>=                          *)
      val _ = op skipPastDot : token located inline stream -> token located
                                                                   inline stream
      (* <utility functions for [[prologReader]]>=    *)
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
               | NONE => (* <fail epically with a diagnostic about [[tokens]]>=
                                                                              *)
                         let exception ThisCan'tHappenCqParserFailed
                             val tokensStrings = map (fn t => " " ^ tokenString
                                                  t) o valOf o peek (many token)
                             val _ = app print (tokensStrings tokens)
                         in  raise ThisCan'tHappenCqParserFailed
                         end
        )                 
      (* Function [[getCq]] tracks the prompt, the mode, and *)
      (* the remaining unread tokens, which together form the *)
      (* [[read_state]]. It also, when called, sets the *)
      (* prompt.                                      *)
      (* <boxed values 111>=                          *)
      val _ = op getCq : read_state -> (cq * read_state) option
      (* Parser [[cq_or_mode]] is always supposed to return *)
      (* something.                                   *)


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

(* Reading clauses and queries while tracking locations *)
(* and modes                                    *)
(*                                              *)
(* All the other languages in this book produce a stream *)
(* of definitions using the [[reader]] function from *)
(* page [->]. We can't reuse that function because it *)
(* doesn't tag tokens with locations and it doesn't keep *)
(* track of modes. Instead, I define a somewhat more *)
(* complex function, [[prologReader]], below. At the *)
(* core of [[prologReader]] is function [[getCq]]. *)
(* <boxed values 108>=                          *)
val _ = op prologReader : bool -> mode -> string * string stream -> cq stream
type read_state  = read_state  fun zz__checktyperead_state (x : read_state ) = (
                               x :  string * mode * token located inline stream)
val _ = op getCq : read_state -> (cq * read_state) option
  in  streamOfUnfold getCq (ps1, initialMode, streamMap INLINE tokens)
  end 
(* The application of [[streamMap INLINE]] may look very *)
(* strange, but many of the utility functions from *)
(* Appendix [->] expect a stream of tokens tagged with *)
(* [[INLINE]]. Even though we don't really need the *)
(* [[INLINE]] for uProlog, it is easier to use a *)
(* meaningless [[INLINE]] than it is to rewrite big *)
(* chunks of Appendix [->].                     *)



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
(*   PRIMITIVES                                                  *)
(*                                                               *)
(*****************************************************************)

(* <primitives ((upr))>=                        *)
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
(* To implement the primitive predicate [[is]], we need *)
(* a very small evaluator. Because it works only with *)
(* integers, never with variables, there is no  *)
(* environment; it's just a tree walk.          *)
(* <boxed values 10>=                           *)
val _ = op eval : term -> int
(* We implement t_1[[ is ]]t_2 by evaluating term t_2 as *)
(* an integer expression and unifying t_1 with the *)
(* result.                                      *)
(* <primitives ((upr))>=                        *)
fun is [x, e] succ fail = (succ (unifyTerm (x, LITERAL (eval e))) fail
                           handle Unify => fail())
  | is _      _    fail = fail ()
(* The parser should arrange that each comparison is *)
(* applied to exactly two arguments. If these arguments *)
(* aren't integers, it's a run-time error.      *)
(* <primitives ((upr))>=                        *)
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

(* Create a tracing version of the interpreter that logs *)
(* every entry to and exit from a Byrd box. Use the *)
(* following functions:                         *)
(* <tracing functions>=                         *)
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

(* <search ((prototype))>=                      *)
fun 'a query database =
  let val builtins = foldl (fn ((n, p), rho) => bind (n, p, rho))
                     emptyEnv ((* Printing a term always succeeds and produces
                                                                          the *)
                               (* identity substitution.
                                                                              *)
                               (* <primops :: ((upr))>=
                                                                              *)
                               ("print", fn args => fn succ => fn fail =>
                                           ( app (fn x => (print (termString x);
                                                                print " ")) args
                                           ; print "\n"
                                           ; succ (fn x => x) fail
                                           )) ::
                               (* <primops :: ((upr))>=
                                                                              *)
                               ("is", is) ::
                               (* <primops :: ((upr))>=
                                                                              *)
                               ("<",  compare "<"  op < ) ::
                               (">",  compare ">"  op > ) ::
                               ("=<", compare "=<" op <= ) ::
                               (">=", compare ">=" op >= ) ::
                               (* Two more predicates, [[!]] and [[not]], cannot
                                                                           be *)
                               (* implemented using this technique; they have to
                                                                           be *)
                               (* added directly to the interpreter (Exercises [
                                                                          ->] *)
                               (*  and [->]). Here we ensure that they can't be
                                                                      used by *)
                               (* mistake.
                                                                              *)
                               (* <primops :: ((upr))>=
                                                                              *)
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
(* Here is the code:                            *)
(* <boxed values 8>=                            *)
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
(* The environment [[builtins]] holds the built-in *)
(* predicates. Because the implementations of these *)
(* predicates are polymorphic ML functions, ML's ``value *)
(* restriction'' prevents us from defining them at top *)
(* level. We therefore have to build the [[builtins]] *)
(* environment dynamically, but as long as we do this *)
(* only once per query, the cost should be acceptable. *)



(*****************************************************************)
(*                                                               *)
(*   INTERACTION                                                 *)
(*                                                               *)
(*****************************************************************)

(* <interaction>=                               *)
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

(* <evaluation ((upr))>=                        *)
fun evalcq prompt (t, database : database, echo) =
  case t
    of USE filename => ((* To read from a file, we read without prompting. If we
                                                                              *)
                        (* fail to open the file, we try adding ``[[.P]]'' to *)
                        (* the name; this is the convention used by XSB Prolog,
                                                                              *)
                        (* a free Prolog interpreter available from the State *)
                        (* University of New York at Stony Brook. If this too *)
                        (* fails, we try adding ``[[.pl]]'' to the name; this is
                                                                              *)
                        (* the convention used by GNU Prolog.           *)
                        (* <read from file [[filename]]>=               *)
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
     | QUERY gs     => ((* To issue a query, we provide success and failure *)
                        (* continuations. The success continuation uses *)
                        (* [[showAndContinue]] to decide if it should resume the
                                                                              *)
                        (* search, looking for another solution, or just declare
                                                                              *)
                        (* victory and stop.                            *)
                        (* <query goals [[gs]] against [[database]]>=   *)
                        query database gs
                          (fn theta => fn resume =>
                             if showAndContinue prompt theta gs then resume()
                                                             else print "yes\n")
                          (fn () => print "no\n"); database)
(* <evaluation ((upr))>=                        *)
and evalPrint prompt (echo, errmsg) (cq, database) =
  let fun continue msg = (errmsg msg; database)
  in  evalcq prompt (cq, database, echo)
      handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
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
(* Processing clauses and queries               *)
(*                                              *)
(* Where another interpreter might use an environment, *)
(* the uProlog interpreter uses a database of clauses. *)
(* <boxed values 9>=                            *)
val _ = op evalcq : bool -> cq * database * (string->unit) -> database
(* To show a solution, we apply the substitution to the *)
(* free varables of the query. If we're prompting, we *)
(* wait for a line of input. If the line begins with a *)
(* semicolon, we continue; otherwise we quit. If we're *)
(* not prompting, we're in batch mode, and we produce at *)
(* most one solution.                           *)
(* <boxed values 9>=                            *)
val _ = op showAndContinue : bool -> subst -> goal list -> bool
(* The read-eval-print loop                     *)
(*                                              *)
(* The read-eval-print loop is much the same as in other *)
(* interpreters, except it takes an additional argument *)
(* that tells whether to prompt. You may have noticed *)
(* this argument in [[]],                       *)
(* which arranges not to prompt inside [[USE]]. *)
(* <boxed values 9>=                            *)
val _ = op evalPrint : bool -> (string->unit) * (string->unit) -> cq * database
                                                                     -> database


(*****************************************************************)
(*                                                               *)
(*   PROLOG COMMAND LINE                                         *)
(*                                                               *)
(*****************************************************************)

(* Command line                                 *)
(*                                              *)
(* uProlog's command-line processor differs from our *)
(* other interpreters, because it has to deal with *)
(* modes. In [[noisy]] state it starts waiting for a *)
(* query, but in quiet state it waits for a rule. *)
(* <Prolog command line>=                       *)
fun runInterpreter noisy = 
  let fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val mode = if noisy then QMODE else RMODE
      val cqs  =
        prologReader noisy mode ("standard input", streamOfLines TextIO.stdIn)
  in  ignore (streamFold (evalPrint noisy (writeln, errorln)) emptyDatabase cqs)
  end 
(* The [[-q]] option is as in other interpreters, and *)
(* the [[-trace]] option turns on tracing.      *)
(* <Prolog command line>=                       *)
fun runmain ["-q"]          = runInterpreter false
  | runmain []              = runInterpreter true
  | runmain ("-trace" :: t) = (tracer := app print; runmain t)
  | runmain _  =
      TextIO.output (TextIO.stdErr, "Usage: " ^ CommandLine.name() ^ " [-q]\n")
(* <Prolog command line>=                       *)
val _ = runmain (CommandLine.arguments())
