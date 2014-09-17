(* Putting all the pieces together              *)
(*                                              *)
(* We stitch together the parts of the implementation in *)
(* this order:                                  *)
(* <haskell.sml>=                               *)


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
(* <boxed values 12>=                           *)
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
(*   HINDLEY-MILNER TYPES                                        *)
(*                                                               *)
(*****************************************************************)

(* The difference between types and type schemes is *)
(* reflected in the abstract syntax:            *)
(* <Hindley-Milner types ((ml/haskell))>=       *)
datatype ty = TYVAR  of name                (* type variable alpha *)
            | TYCON  of name                (* type constructor mu *)
            | CONAPP of ty * ty list        (* type-level application *)

datatype type_scheme = FORALL of name list * ty
(* <Hindley-Milner types ((ml/haskell))>=       *)
type subst = ty env
fun varsubst theta = 
  (fn a => find (a, theta) handle NotFound _ => TYVAR a)
(* <boxed values 23>=                           *)
type subst = subst
val _ = op varsubst : subst -> (name -> ty)
(* As the code shows, the function defined by a *)
(* substitution is total. If a type variable is not in *)
(* the domain of the substitution, the function leaves *)
(* that variable unchanged.                     *)

(* <Hindley-Milner types ((ml/haskell))>=       *)
fun tysubst theta =
  let fun subst (TYVAR a) = varsubst theta a
        | subst (TYCON c) = TYCON c
        | subst (CONAPP (tau, taus)) = CONAPP (subst tau, map subst taus)
(* The most frequently used interpretation of a *)
(* substitution is as a function from types to types. *)
(* That interpretation is provided by function  *)
(* [[tysubst]]. The code is almost exactly the same as *)
(* the code in Chapter [->]. [*]                *)
(* <boxed values 24>=                           *)
val _ = op tysubst : subst -> (ty -> ty)
val _ = op subst   :           ty -> ty
  in  subst
  end
(* <Hindley-Milner types ((ml/haskell))>=       *)
(* <sets of free type variables ((ml/haskell))>= *)
type 'a set = 'a list
val emptyset = []
fun member x = 
  List.exists (fn y => y = x)
fun insert (x, ys) = 
  if member x ys then ys else x::ys
fun union (xs, ys) = foldl insert ys xs
fun inter (xs, ys) =
  List.filter (fn x => member x ys) xs
fun diff  (xs, ys) = 
  List.filter (fn x => not (member x ys)) xs
(* Sets of type variables                       *)
(*                                              *)
(* Much of type inference manipulates sets of type *)
(* variables. We provide a simple implementation that *)
(* represents a set using a list with no duplicate *)
(* elements. [The~\ml~types of the set operations *)
(* include type variables with double primes, like~ *)
(* [[''a]]. The type variable~[[''a]] can be    *)
(* instantiated only with an ``equality type.'' Equality *)
(* types include base types like strings and integers, *)
(* as well as user-defined types that do not contain *)
(* functions. Functions \emph{cannot} be compared for *)
(* equality.]                                   *)
(* <boxed values 30>=                           *)
type 'a set = 'a set
val _ = op emptyset : 'a set
val _ = op member   : ''a -> ''a set -> bool
val _ = op insert   : ''a     * ''a set  -> ''a set
val _ = op union    : ''a set * ''a set  -> ''a set
val _ = op inter    : ''a set * ''a set  -> ''a set
val _ = op diff     : ''a set * ''a set  -> ''a set
(* <sets of free type variables ((ml/haskell))>= *)
fun freetyvars t =
  let fun f (TYVAR v,          ftvs) = insert (v, ftvs)
        | f (TYCON _,          ftvs) = ftvs
        | f (CONAPP (ty, tys), ftvs) = foldl f (f (ty, ftvs)) tys
  in  rev (f (t, emptyset))
  end  
(* The function [[freetyvars]] computes the free type *)
(* variables of a type. For readability, I ensure that *)
(* type variables appear in the set in the order of *)
(* their first appearance in the type, when reading from *)
(* left to right.                               *)
(* <boxed values 31>=                           *)
val _ = op freetyvars : ty -> name set
fun dom theta = map (fn (a, _) => a) theta
fun compose (theta2, theta1) =
  let val domain  = union (dom theta2, dom theta1)
      val replace = tysubst theta2 o varsubst theta1
  in  map (fn a => (a, replace a)) domain
  end
(* A function produced by [[tysubst]] has type [[ty -> *)
(* ty]] and so can be composed with any other function *)
(* of the same type, including all functions that *)
(* correspond to substitutions. To be precise, if \subsn *)
(* _1 and \subsn_2 are substitutions, then tysubst \ *)
(* subsn_2 otysubst \subsn_1 is a function from types to *)
(* types (and also corresponds to a substitution). *)
(* Composition is really useful, but a substitution data *)
(* structure \subsn is strictly more useful than the *)
(* corresponding function tysubst \subsn. For one thing, *)
(* we can interrogate \subsn about its domain. To have *)
(* the best of both worlds, I define a function for *)
(* composing substitutions, which obeys the algebraic *)
(* law                                          *)
(*                                              *)
(*  tysubst(compose(\subsn_2, \subsn_1)) = tysubst \ *)
(*  subsn_2 otysubst \subsn_1.                  *)
(*                                              *)
(* Function [[dom]] produces a substitution's domain. *)
(* <boxed values 25>=                           *)
val _ = op dom     : subst -> name set
val _ = op compose : subst * subst -> subst
(* <Hindley-Milner types ((ml/haskell))>=       *)
exception BugInTypeInference of string

fun instantiate (FORALL (formals, tau), actuals) =
  tysubst (bindList (formals, actuals, emptyEnv)) tau
  handle BindListLength => raise BugInTypeInference
                                              "number of types in instantiation"
(* Instantiation is just as in Chapter [->], except no *)
(* kind environment is needed. Because the system *)
(* ensures everything has the right kind, it is an *)
(* internal error to instantiate with the wrong number *)
(* of arguments. The internal error is signalled by *)
(* raising the exception [[BugInTypeInference]]. *)
(* This exception is raised only when there is a fault *)
(* in the interpreter; a faulty uML program should never *)
(* trigger this exception. [*]                  *)
(* <boxed values 26>=                           *)
val _ = op instantiate : type_scheme * ty list -> ty
(* <Hindley-Milner types ((ml/haskell))>=       *)
val idsubst = emptyEnv
(* <Hindley-Milner types ((ml/haskell))>=       *)
infix 7 |-->
val idsubst = emptyEnv
fun a |--> (TYVAR a') = if a = a' then idsubst else bind (a, TYVAR a', emptyEnv)
  | a |--> tau        = if member a (freetyvars tau) then
                          raise BugInTypeInference "non-idempotent substitution"
                        else
                          bind (a, tau, emptyEnv)
(* I finish this section with three more definitions *)
(* related to substitutions. These definitions provide *)
(* the empty substitution [[idsubst]] as well as two *)
(* functions used to create and change substitutions. *)
(* The substitution that maps every type variable to *)
(* itself is sometimes called the empty substitution *)
(* (because its domain is empty) and sometimes the *)
(* identity substitution (because when viewed as a *)
(* function from types to types, it is the identity *)
(* function). In code it is [[idsubst]]; in math it is \ *)
(* idsubst, and it obeys the algebraic law \idsubsno\ *)
(* subsn= \subsno\idsubsn= \subsn.              *)
(* <boxed values 27>=                           *)
val _ = op idsubst : subst
(* The simplest substitutions are those that substitute *)
(* a single type for a single variable. To make it easy *)
(* to create such a substitution, I define a new infix *)
(* operator [[|?>]]. The expression [[alpha |?> tau]] is *)
(* the substitution that substitutes [[tau]] for *)
(* [[alpha]]. In math, we write that substitution \ *)
(* xsubsnalphatau.                              *)
(* <boxed values 27>=                           *)
val _ = op |--> : name * ty -> subst
(* The [[|?>]] function doesn't accept just any alpha *)
(*  and tau. It produces a substitution \xsubsnalphatau *)
(* only when type variable alpha is not free in tau. *)
(* It's a little hard to motivate this limitation, but *)
(* the idea is to ensure that the [[|?>]] function *)
(* produces only idempotent substitutions. An idempotent *)
(* substitution \subsn has the property that    *)
(*                                              *)
(*  \subsno\subsn= \subsn.                      *)
(*                                              *)
(* Idempotence by itself is not so interesting, but if \ *)
(* subsn= \xsubsnalphatau is idempotent, then we are *)
(* guaranteed the following equality between types: *)
(*                                              *)
(*  \subsnalpha= \subsntau.                     *)
(*                                              *)
(* Because type inference is all about using    *)
(* substitutions to guarantee equality of types, we want *)
(* to be sure that every substitution we create is *)
(* idempotent. (An example of a substitution that is not *)
(* idempotent is \xsubsnalphalistalpha.)        *)

(* <Hindley-Milner types ((ml/haskell))>=       *)
(* <printing types ((ml/haskell))>=             *)
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
  (* precedences *)
  val CONp   = 3
  val STARp  = 2
  val ARROWp = 1
  val NONEp  = 0
  
  fun parens s = "(" ^ s ^ ")"
  fun bracket (s, context, prec) = if prec <= context then parens s else s
  fun p (context, CONAPP (TYCON "tuple", l)) = bracket (ptuple l, context, STARp
                                                                               )
    | p (context, CONAPP (TYCON "function", [arg, ret])) = 
          bracket (p (ARROWp, arg) ^ " -> " ^ p (ARROWp, ret), context, ARROWp)
    | p (context, CONAPP (n, []))  = p (context, n)
    | p (context, CONAPP (n, [t])) = p (CONp, t) ^ " " ^ p (CONp, n)
    | p (context, CONAPP (n, l)) = 
          "(" ^ separate ("", ", ") (map typeString l) ^ ") " ^ p (CONp, n)
    | p (context, TYCON n) = n
    | p (context, TYVAR v) = "'" ^ v
  and ptuple l = separate ("unit", " * ") (map (fn t => p (STARp, t)) l)
  and typeString ty = p (NONEp, ty)
in 
  val typeString = typeString
  val ptuple = ptuple
end
fun typeSchemeString (FORALL ([], ty)) =
      typeString ty
  | typeSchemeString (FORALL (a::a's, ty)) =
      let fun combine (var, vars) = vars ^ ", '" ^ var
      in  "forall " ^ foldl combine ("'" ^ a) a's ^ " . " ^ typeString ty
      end
(* Other functions to manipulate types          *)
(*                                              *)
(* Appendix [->] defines a function [[typeString]], *)
(* which we use to print types. We also use this *)
(* function to print type schemes, but when we print a *)
(* true polytype, we make the forall explicit, and *)
(* we show all the quantified variables. [It~is not *)
(* strictly necessary to show the quantified variables, *)
(* because in any top-level type, \emph{all} type *)
(* variables are quantified by the~$\forall$. For this *)
(* reason, Standard~ML leaves out quantifiers and type *)
(* variables. But when you're learning about parametric *)
(* polymorphism, it's better to make the \texttt{forall} *)
(* s explicit. ]                                *)
(* <boxed values 28>=                           *)
val _ = op typeString       : ty          -> string
val _ = op typeSchemeString : type_scheme -> string
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun eqType (TYCON c, TYCON c') = c = c'
  | eqType (CONAPP (tau, taus), CONAPP (tau', taus')) =
      eqType (tau, tau') andalso eqTypes (taus, taus')
  | eqType (TYVAR a, TYVAR a') = a = a'
  | eqType _ = false
and eqTypes (t::taus, t'::taus') = eqType (t, t') andalso eqTypes (taus, taus')
  | eqTypes ([], []) = true
  | eqTypes _ = false
(* <Hindley-Milner types ((ml/haskell))>=       *)
val inttype  = TYCON "int"
val booltype = TYCON "bool"
val symtype  = TYCON "sym"
val alpha    = TYVAR "a"
val beta     = TYVAR "b"
fun tupletype taus  = CONAPP (TYCON "tuple", taus)
fun pairtype (x, y) = tupletype [x, y]
val unittype        = tupletype []
fun listtype ty     = CONAPP (TYCON "list", [ty])
fun funtype (args, result) = 
  CONAPP (TYCON "function", [tupletype args, result])
(* Because there are no quantifiers in a type, the *)
(* definition of type equality is simpler than the *)
(* corresponding definition for Typed uScheme in chunk  *)
(* [->].                                        *)
(* <boxed values 29>=                           *)
val _ = op eqType : ty * ty -> bool
(* To make it easier to define the primitive operations *)
(* of uML, I provide convenience functions very much *)
(* like those from Chapter [->].                *)
(* <boxed values 29>=                           *)
val _ = op inttype   : ty
val _ = op booltype  : ty
val _ = op symtype   : ty
val _ = op unittype  : ty
val _ = op listtype  : ty -> ty
val _ = op tupletype : ty list -> ty
val _ = op pairtype  : ty * ty -> ty
val _ = op funtype   : ty list * ty -> ty
val _ = op alpha     : ty
val _ = op beta      : ty
(* <Hindley-Milner types ((ml/haskell))>=       *)
local
  val n = ref 1
in
  fun freshtyvar _ = TYVAR ("t" ^ Int.toString (!n) before n := !n + 1)
(* <boxed values 32>=                           *)
val _ = op freshtyvar : 'a -> ty
end
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun canonicalize (FORALL (bound, ty)) =
  let fun canonicalTyvarName n =
        if n < 26 then str (chr (ord #"a" + n))
        else "v" ^ Int.toString (n - 25)
      val free = diff (freetyvars ty, bound)
      fun unusedIndex n =
        if member (canonicalTyvarName n) free then unusedIndex (n+1) else n
      fun newBoundVars (index, [])                = []
        | newBoundVars (index, oldvar :: oldvars) =
            let val n = unusedIndex index
            in  canonicalTyvarName n :: newBoundVars (n+1, oldvars)
            end
      val newBound = newBoundVars (0, bound)
(* Canonical type schemes                       *)
(*                                              *)
(* Type variables like [['t136]] are not very readable *)
(* in error messages. A type scheme like \monoforall *)
(* 't136 . 't136 list -> int is unpleasant to look at, *)
(* and it is completely interchangeable with the *)
(* equivalent type scheme \monoforall 'a . 'a list -> *)
(* int. The two schemes are equivalent because if a type *)
(* variable is \/-bound, its name is irrelevant. For *)
(* readability, we are better off using the names *)
(* [['a]], [['b]], etc., for bound type variables. The *)
(* function [[canonicalize]] renames bound type *)
(* variables in a type scheme. We replace each existing *)
(* bound type variable with a canonically named type *)
(* variable, being careful not to use the name of any *)
(* free type variable.                          *)
(* <boxed values 33>=                           *)
val _ = op canonicalize : type_scheme -> type_scheme
val _ = op newBoundVars : int * name list -> name list
  in  FORALL (newBound, tysubst (bindList (bound, map TYVAR newBound, emptyEnv))
                                                                             ty)
  end
(* The function [[unusedIndex]] finds a name for a bound *)
(* type variable; it ensures that the name is not the *)
(* name of any free type variable.              *)

(* <Hindley-Milner types ((ml/haskell))>=       *)
fun generalize (tau, tyvars) =
  canonicalize (FORALL (diff (freetyvars tau, tyvars), tau))
(* <boxed values 34>=                           *)
val _ = op generalize : ty * name set -> type_scheme
(* [*]                                          *)

(* <Hindley-Milner types ((ml/haskell))>=       *)
fun freshInstance (FORALL (bound, tau)) =
  instantiate (FORALL (bound, tau), map freshtyvar bound)
(* The dual function, [[instantiate]], is defined in *)
(* chunk [->]. It requires a list of types with which to *)
(* instantiate, but the common case is to instantiate *)
(* with fresh type variables. Function [[freshInstance]] *)
(* implements this case.                        *)
(* <boxed values 35>=                           *)
val _ = op freshInstance : type_scheme -> ty
(* Constraints                                  *)
(*                                              *)
(* To highlight the relationship between the code and *)
(* the math, I've chosen a representation that's close *)
(* to the math: [Experienced type-system hackers might *)
(* prefer a list of pairs of types, but a list of pairs *)
(* is easy to work with only if you already understand *)
(* what's going on.] the \eqty operator is [[=*=]]; the  *)
(* \land operator is [[/                        *)
(* ]; and the \trivc constraint is [[TRIVIAL]]. [*] *)
(* <Hindley-Milner types ((ml/haskell))>=       *)
datatype con = =*= of ty  * ty
             | /\  of con * con
             | TRIVIAL
infix 4 =*=
infix 3 /\
(* <Hindley-Milner types ((ml/haskell))>=       *)
(* A constraint can be printed in full, but it's easier *)
(* to read if its first passed to [[untriviate]], which *)
(* removes as many [[TRIVIAL]] sub-constraints as *)
(* possible.                                    *)
(* <printing constraints ((ml/haskell))>=       *)
fun untriviate (c /\ c') = (case (untriviate c, untriviate c')
                              of (TRIVIAL, c) => c
                               | (c, TRIVIAL) => c
                               | (c, c') => c /\ c')
  | untriviate atomic = atomic

fun constraintString (c /\ c')  = constraintString c ^ " /\\ " ^
                                                             constraintString c'
  | constraintString (t =*= t') = typeString t ^ " =*= " ^ typeString t'
  | constraintString TRIVIAL = "TRIVIAL"
(* Appendix [->] defines a function             *)
(* [[constraintString]], which we use to print  *)
(* constraints. It also defines a function      *)
(* [[untriviate]], which removes all trivial conjuncts *)
(* from a constraint.                           *)
(* <boxed values 36>=                           *)
val _ = op constraintString : con -> string
(* Now that we can represent constraints, we can find *)
(* free type variables in a constraint, and we can *)
(* substitute for free type variables.          *)
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun freetyvarsConstraint (t =*= t') = union (freetyvars t, freetyvars t')
  | freetyvarsConstraint (c /\  c') = union (freetyvarsConstraint c,
                                             freetyvarsConstraint c')
  | freetyvarsConstraint TRIVIAL    = emptyset
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun consubst theta =
  let fun subst (tau1 =*= tau2) = tysubst theta tau1 =*= tysubst theta tau2
        | subst (c1 /\ c2)      = subst c1 /\ subst c2
        | subst TRIVIAL         = TRIVIAL
  in  subst
  end
(* A substitution is applied to a constraint using the *)
(* following rules: {mathpar} \subsn(tau_1\eqtytau_2) = *)
(* \subsntau_1 \eqty\subsntau_2                 *)
(*                                              *)
(* \subsn(\tyc_1 \land\tyc_2) = \subsn\tyc_1 \land\subsn *)
(* \tyc_2                                       *)
(*                                              *)
(* \subsn\trivc= \trivc {mathpar} The code is quite *)
(* similar to the code for [[tysubst]] in chunk [->].  *)
(* [*]                                          *)
(* <boxed values 37>=                           *)
val _ = op consubst : subst -> con -> con
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun conjoinConstraints []      = TRIVIAL
  | conjoinConstraints [c]     = c
  | conjoinConstraints (c::cs) = c /\ conjoinConstraints cs
(* We implement the \bigwedge{ ...} operator using the *)
(* ML function [[conjoinConstraints]]. I avoid using *)
(* [[foldr]] or [[foldr]] because I want to preserve the *)
(* number and order of sub-constraints.         *)
(* <boxed values 38>=                           *)
val _ = op conjoinConstraints : con list -> con
(* Constraint solving                           *)
(*                                              *)
(* Our type-inference algorithm is built on a constraint *)
(* solver, which given a constraint \tyc produces a *)
(* substitution \subsn such that \subsn\tyc is trivially *)
(* satisfied. But if the algorithm is given an ill-typed *)
(* program, it produces an unsolvable constraint: one *)
(* for which no such \subsn exists. Examples of *)
(* unsolvable constraints include int\eqtybool and list *)
(* alpha\eqtyalpha. When we discover an unsolvable *)
(* constraint, we want to issue a readable error *)
(* message, which shouldn't be full of machine-generated *)
(* fresh type variables. To do so, we should take the *)
(* pair of types that can't be made equal, and we should *)
(* put the pair into canonical form. Function   *)
(* [[unsatisfiableEquality]] does just that, by putting *)
(* the two types together into a pair type. [*] *)
(* <Hindley-Milner types ((ml/haskell))>=       *)
exception TypeError of string

fun unsatisfiableEquality (t1, t2) =
  case canonicalize (FORALL (union (freetyvars t1, freetyvars t2), tupletype [t1
                                                                         , t2]))
    of FORALL (_, CONAPP (TYCON "tuple", [t1, t2])) => 
         raise TypeError ("cannot make " ^ typeString t1 ^ " equal to " ^
                                                                  typeString t2)
     | _ => let exception ThisCan'tHappen in raise ThisCan'tHappen end
(* <Hindley-Milner types ((ml/haskell))>=       *)
(* <constraint solving ((prototype))>=          *)
exception LeftAsExercise of string
fun solve c = raise LeftAsExercise "solve"
(* <boxed values 39>=                           *)
val _ = op solve : con -> subst
(* <constraint solving>=                        *)
(*asdf*)
(* Function [[freetyvarsGamma]] finds the type variables *)
(* free in Gamma, i.e., the type variables free in any  *)
(* sigma in Gamma. We need [[freetyvarsGamma]] to get a *)
(* set of free type variables to use in [[generalize]]; *)
(* when we assign a type scheme to a let-bound variable, *)
(* only those type variables not free in Gamma may be \/ *)
(* -bound. If [[freetyvarsGamma]] were implemented over *)
(* a simple representation of type [[type_scheme env]], *)
(* it would visit every type scheme in every binding in *)
(* the environment. Because most bindings contribute no *)
(* free type variables, most visits would be    *)
(* unnecessary. We therefore make an optimization: with *)
(* every type environment, we keep a cache of the free *)
(* type variables. Our representation of type   *)
(* environments is therefore as follows:        *)
(* <Hindley-Milner types ((ml/haskell))>=       *)
type type_env = type_scheme env * name set
(* <Hindley-Milner types ((ml/haskell))>=       *)
val emptyTypeEnv = 
      (emptyEnv, emptyset)
fun findtyscheme (v, (Gamma, free)) = find (v, Gamma)
(* We create an empty type environment that binds no *)
(* variables and has no free type variables. And when we *)
(* try to find a type scheme, we ignore the free *)
(* variables.                                   *)
(* <boxed values 41>=                           *)
val _ = op emptyTypeEnv : type_env
val _ = op findtyscheme : name * type_env -> type_scheme
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun bindtyscheme (v, sigma as FORALL (bound, tau), (Gamma, free)) = 
  (bind (v, sigma, Gamma), union (diff (freetyvars tau, bound), free))
(* <Hindley-Milner types ((ml/haskell))>=       *)
fun freetyvarsGamma (_, free) = free
(* <Hindley-Milner types ((haskell))>=          *)
val valtype = TYCON "value"
(* <Hindley-Milner types ((haskell))>=          *)
fun iotype ty  = CONAPP (TYCON "io", [ty])
(* <Hindley-Milner types ((haskell))>=          *)
fun solve (TRIVIAL)  = idsubst
  | solve (c1 /\ c2) =
      let val theta1 = solve c1
          val theta2 = solve (consubst theta1 c2)
      in  compose (theta2, theta1)
      end
  | solve (tau =*= tau') =
      case (tau, tau')
        of (TYVAR a, tau) => solveTyvarEq (a, tau)
         | (tau, TYVAR a) => solveTyvarEq (a, tau)
         | (TYCON mu, TYCON mu') => if mu = mu' then idsubst
                                    else unsatisfiableEquality (tau, tau')
         | (CONAPP (t, ts), CONAPP (t', ts')) =>
             let fun eqAnd (t, t', c) = t =*= t' /\ c
             in  solve (ListPair.foldlEq eqAnd TRIVIAL (t::ts, t'::ts'))
                 handle ListPair.UnequalLengths => unsatisfiableEquality (tau,
                                                                           tau')
             end
         | _ => unsatisfiableEquality (tau, tau')

and solveTyvarEq (a, tau) = 
      if eqType (TYVAR a, tau) then
        idsubst
      else if member a (freetyvars tau) then
        unsatisfiableEquality (TYVAR a, tau)
      else
        a |--> tau

fun isStandard pairs =
  let fun distinct a' (a, tau) = a <> a' andalso not (member a' (freetyvars tau)
                                                                               )
      fun good (prev', (a, tau)::next) =
            List.all (distinct a) prev' andalso List.all (distinct a) next
            andalso good ((a, tau)::prev', next)
        | good (_, []) = true
  in  good ([], pairs)
  end

val solve =
  fn c => let val theta = solve c
          in  if isStandard theta then theta
              else raise BugInTypeInference "non-standard substitution"
          end


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
(* <boxed values 51>=                           *)
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
(* <boxed values 52>=                           *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a streams is read, no new actions are performed. *)
(* <boxed values 52>=                           *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* <boxed values 53>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such stream, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 53>=                           *)
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
(* <boxed values 54>=                           *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* <streams>=                                   *)
type line = string
fun streamOfLines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 55>=                           *)
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
(* <boxed values 56>=                           *)
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
(* <boxed values 57>=                           *)
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
(* <boxed values 58>=                           *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* <boxed values 58>=                           *)
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
(* <boxed values 59>=                           *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 60>=                           *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right: [*]                                   *)
(* <boxed values 61>=                           *)
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
(* <boxed values 62>=                           *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 62>=                           *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 63>=                           *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 64>=                           *)
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
(* <boxed values 65>=                           *)
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
(* <boxed values 66>=                           *)
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
(* <boxed values 67>=                           *)
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
(* <boxed values 67>=                           *)
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
(* <boxed values 68>=                           *)
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
(* <boxed values 69>=                           *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* has a special operator [[<>]], which is also *)
(* pronounced ``applied to.'' It combines a B-to-C *)
(* function with an \atob transformer to produce an \ *)
(* atoc transformer.                            *)
(* <boxed values 70>=                           *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* <boxed values 71>=                           *)
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
(* <boxed values 72>=                           *)
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
(* <boxed values 73>=                           *)
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
(* <boxed values 74>=                           *)
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
(* <boxed values 75>=                           *)
val _ = op eos : ('a, unit) xformer
(* <parsing combinators>=                       *)
fun peek tx xs = case tx xs of SOME (OK y, _) => SOME y
                             | _ => NONE
(* It can also be useful to peek at the contents of a *)
(* stream, without looking at any input, and while *)
(* ignoring errors.                             *)
(* <boxed values 76>=                           *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* <parsing combinators>=                       *)
fun rewind tx xs = case tx xs of SOME (ey, _) => SOME (ey, xs)
                               | NONE => NONE
(* And we might want to transform some input, then *)
(* rewind it back to the starting point. (Actions can't *)
(* be undone, but at least the input can be read again.) *)
(* <boxed values 77>=                           *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* <boxed values 78>=                           *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <parsing combinators>=                       *)
fun oneEq x = sat (fn x' => x = x') one
(* <boxed values 79>=                           *)
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
(* <boxed values 80>=                           *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* <boxed values 81>=                           *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* <parsing combinators>=                       *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* <boxed values 82>=                           *)
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
(* <boxed values 83>=                           *)
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
(* <boxed values 84>=                           *)
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
(* <boxed values 85>=                           *)
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
(* <boxed values 86>=                           *)
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
(* <boxed values 87>=                           *)
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
(* <boxed values 88>=                           *)
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
(* <boxed values 89>=                           *)
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
(* <boxed values 90>=                           *)
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
(* <boxed values 91>=                           *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* <boxed values 92>=                           *)
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
(* <boxed values 93>=                           *)
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
(* <boxed values 93>=                           *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To signal an error at a given location, call *)
(* [[errorAt]].                                 *)
(* <boxed values 93>=                           *)
val _ = op errorAt : string -> srcloc -> 'a error
(* We can pair source-code locations with individual *)
(* lines and tokens. To make it easier to read the *)
(* types, I define a type abbreviation which says that a *)
(* value paired with a location is ``located.'' *)
(* <boxed values 93>=                           *)
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
(* <boxed values 94>=                           *)
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
(* <boxed values 95>=                           *)
type 'a inline = 'a inline
val _ = op drainLine : 'a inline stream -> 'a inline stream
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <boxed values 95>=                           *)
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
(* <boxed values 95>=                           *)
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
(* <boxed values 96>=                           *)
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
(* <boxed values 97>=                           *)
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
(* <boxed values 98>=                           *)
val _ = op <!> : 'a parser * string -> 'b parser
(* Keywords, brackets, and other literals       *)
(*                                              *)
(* It's extremely common to want to recognize literal *)
(* tokens, like the keyword [[if]] or a left or right *)
(* parenthesis. The [[literal]] parser accepts any token *)
(* whose concrete syntax is an exact match for the given *)
(* string argument.                             *)
(* <boxed values 98>=                           *)
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
(* <boxed values 99>=                           *)
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
(* <boxed values 100>=                          *)
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
(* <boxed values 101>=                          *)
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
(* <boxed values 102>=                          *)
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
(* <boxed values 103>=                          *)
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
(* <boxed values 104>=                          *)
val _ = op echoTagStream : line stream -> line stream 
(* <an interactive reader>=                     *)
fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
(* Lexing and parsing with error handling       *)
(*                                              *)
(* The next step is error handling. When the code *)
(* detects an error it prints a message using function *)
(* [[errorln]].                                 *)
(* <boxed values 105>=                          *)
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
(* <boxed values 106>=                          *)
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
(* <boxed values 107>=                          *)
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
(* <boxed values 108>=                          *)
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
(* <boxed values 109>=                          *)
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
(* <boxed values 110>=                          *)
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
  (* <boxed values 112>=                          *)
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
(* <boxed values 111>=                          *)
val _ = op schemeToken : token lexer
val _ = op atom : string -> token
end


(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES                                  *)
(*                                                               *)
(*****************************************************************)

(* Values and abstract syntax                   *)
(*                                              *)
(* Unlike an eager language, Haskell does not always *)
(* compute with values. What a name stands for, whether *)
(* it is a let-bound name or a formal parameter, is a *)
(* mutable location [[loc]], which may contain a *)
(* [[value]] or an unevaluated [[thunk]]. If a [[loc]] *)
(* does contain a thunk, we can evaluate the thunk and *)
(* then replace the thunk with a [[value]]. Almost *)
(* everything that we were used to thinking of as a *)
(* value is now a [[loc]], except:              *)
(*                                              *)
(*   * Primitive operators and [[eval]] always return a *)
(*  [[value]], never a thunk.                   *)
(*   * Literal values are never lazy, so [[LITERAL]] *)
(*  contains [[value]].                         *)
(*                                              *)
(* <abstract syntax and values ((haskell))>=    *)
datatype thunk_contents 
  = VALUE       of value
  | IN_PROGRESS
  | UNEVAL       of thunk
and value (* a value in weak head normal form *)
  = VCON of name * loc list   (* fully saturated constructor app *)
  | SYM  of name
  | NUM  of int
  | CLOSURE   of lambda * loc env
  | PRIMITIVE of primitive
  | IO        of unit -> loc  (* monadic action *)
and exp 
  = LITERAL of value
  | VAR     of name
  | APPLY   of exp * exp list
  | LETX    of let_kind * (name * exp) list * exp
  | DO      of            (name * exp) list * exp
  | LAMBDA  of lambda
  | CASE    of exp * match list
  | IFX     of exp * exp * exp
and let_kind = LET | LETREC | LETSTAR
 withtype loc       = thunk_contents ref
      and lambda    = name list * exp
      and thunk     = exp * thunk_contents ref env
      and match     = (name * name list) * exp
      and primitive = thunk_contents ref list -> value
exception RuntimeError of string (* error message *)
exception Unimp of string
(* <abstract syntax and values ((haskell))>=    *)
datatype def = VAL    of name * exp
             | VALREC of name * exp
             | EXP    of exp
             | DEFINE of name * lambda
             | CONDEF of name * type_scheme
             | USE    of name


(*****************************************************************)
(*                                                               *)
(*   VALUES                                                      *)
(*                                                               *)
(*****************************************************************)

(* <values ((haskell))>=                        *)
fun allocThunk (e, rho) = ref (UNEVAL (e, rho))
fun allocValue v        = ref (VALUE v)
(* Here are two convenience functions for allocating new *)
(* locations:                                   *)
(* <boxed values 1>=                            *)
val _ = op allocThunk : exp * loc env -> loc
val _ = op allocValue : value         -> loc
(* <values ((haskell))>=                        *)
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
fun locString (ref IN_PROGRESS) = "_|_"
  | locString (ref (UNEVAL _))  = "..."
  | locString (ref (VALUE v))  = valueString v
and valueString (VCON ("cons", [l, ls])) = (* As in other interpreters, we have
                                                             a special way of *)
                                           (* printing applications of [[cons]].
                                                                              *)
                                           (* <convert [[(cons l ls)]] to string
                                                                   >=         *)
                                           let fun tail (VCON ("cons", [l, ls]))
                                                = " " ^ locString l ^ tailLoc ls
                                                 | tail (VCON ("()", []))
                                                                           = ")"
                                                 | tail v
                                                   = " . " ^ valueString v ^ ")"
                                               and tailLoc (ref (VALUE v))   =
                                                                          tail v
                                                 | tailLoc (ref IN_PROGRESS) =
                                                                         " _|_)"
                                                 | tailLoc (ref (UNEVAL _))  =
                                                                       " . ...)"
                                           in  "(" ^ locString l ^ tailLoc ls
                                           end
  | valueString (VCON (c, []))  = c
  | valueString (VCON (c, ls))  = "(" ^ c ^ " " ^ spaceSep (map locString ls) ^
                                                                             ")"
  | valueString (NUM n      )   = String.map (fn #"~" => #"-" | c => c) (
                                                                 Int.toString n)
  | valueString (SYM v      )   = v
  | valueString (CLOSURE   _)   = "<procedure>"
  | valueString (PRIMITIVE _)   = "<procedure>"
  | valueString (IO _       )   = "<I/O action>"
(* And here is where we print the contents of a *)
(* location.                                    *)
(* <boxed values 2>=                            *)
val _ = op locString   : loc   -> string
val _ = op valueString : value -> string


(*****************************************************************)
(*                                                               *)
(*   PARSING                                                     *)
(*                                                               *)
(*****************************************************************)

(* <parsing ((haskell))>=                       *)
val lambdaDups   = nodups ("formal parameter", "lambda")
val conDups      = nodups ("argument of constructor", "case expression")

fun letDups LETSTAR (loc, bindings) = OK bindings
  | letDups kind    (loc, bindings) =
      let val names    = map (fn (n, _) => n) bindings
          val kindName = case kind of LET => "let" | LETREC => "letrec" | _ =>
                                                                            "??"
      in  nodups ("bound name", kindName) (loc, names) >>=+ (fn _ => bindings)
      end
(* <parsing ((haskell))>=                       *)
fun embedList []     = VCON ("()", [])
  | embedList (h::t) = VCON ("cons", [allocValue h, allocValue (embedList t)])
(* When parsing a list of values, we need to convert it *)
(* to a uHaskell list.                          *)
(* <boxed values 120>=                          *)
val _ = op embedList : value list -> value
(* <parsing ((haskell))>=                       *)
val name    = (fn (NAME  n) => SOME n  | _ => NONE) <$>? token
val booltok = (fn (SHARP b) => SOME b  | _ => NONE) <$>? token
val int     = (fn (INT   n) => SOME n  | _ => NONE) <$>? token
val quote   = (fn (QUOTE)   => SOME () | _ => NONE) <$>? token

fun boolcon p = VCON (if p then "#t" else "#f", [])

fun exp tokens = (
     VAR              <$> name
 <|> (LITERAL o NUM)  <$> int
 <|> (LITERAL o boolcon) <$> booltok
 <|> LITERAL          <$> (quote *> sexp)
 <|> bracket "if"     "(if e1 e2 e3)"            (curry3 IFX <$> exp <*> exp <*>
                                                                            exp)
 <|> bracket "lambda" "(lambda (names) body)"    (     lambda  <$> @@ formals
                                                                       <*>! exp)
 <|> bracket "let"    "(let (bindings) body)"    (letx LET     <$> @@ bindings
                                                                       <*>! exp)
 <|> bracket "letrec" "(letrec (bindings) body)" (letx LETREC  <$> @@ bindings
                                                                       <*>! exp)
 <|> bracket "let*"   "(let* (bindings) body)"   (letx LETSTAR <$> @@ bindings
                                                                       <*>! exp)
 <|> bracket "case"   "(case exp matches)"       (curry CASE   <$> exp <*> many
                                                                          match)
 <|> "(" >-- literal ")" <!> "empty application"
 <|> curry APPLY <$> "(" >-- exp <*> many exp --< ")"
) tokens
and lambda xs exp =
  nodups ("formal parameter", "lambda") xs >>=+ (fn xs => LAMBDA (xs, exp))
and letx kind bs exp = letDups kind bs >>=+ (fn bs => LETX (kind, bs, exp))
and formals  ts = ("(" >-- many name --< ")") ts
and bindings ts = ("(" >-- (many binding --< ")" <?> "(x e)...")) ts
and binding  ts = ("(" >-- (pair <$> name <*> exp --< ")" <?>
                                                        "(x e) in bindings")) ts

and match ts = ("(" >-- (pair <$> matchlhs <*> exp --< ")" <?>
                                                        "(pat exp) in case")) ts
and matchlhs ts = 
   (  (fn n => (n, [])) <$> name
   <|> ("()", []) <$ "(" >-- literal ")"
   <|> pair <$> "(" >-- name <*> (conDups <$>! @@ (many name)) --< ")"
   ) ts
                
and sexp tokens = (
     SYM <$> (notDot <$>! name)
 <|> NUM          <$> int
 <|> boolcon      <$> booltok
 <|> (fn v => embedList [SYM "quote", v]) <$> (quote *> sexp)
 <|> embedList    <$> "(" >-- many sexp --< ")"
) tokens
and notDot "." = ERROR
                      "this interpreter cannot handle . in quoted S-expressions"
  | notDot s   = OK s
(* <parsing ((haskell))>=                       *)
fun unexpected msg (loc, _) = errorAt loc msg
val tyvar = curry op ^ "'" <$> (quote *> (name <?> "type variable"))

fun keyword syntax words =
  let fun isKeyword s = List.exists (fn s' => s = s') words
  in  (fn (NAME n) => if isKeyword n then SOME n else NONE | _ => NONE) <$>?
                                                                           token
  end

val expKeyword = keyword "type"       ["if", "lambda",
                                       "type-lambda", "let", "let*", "letrec"]

fun checkedForall tyvars tau =
  nodups ("quantified type variable", "forall") tyvars >>=+ 
  (fn a's => FORALL (a's, tau))

fun ty tokens = (
     TYCON <$> name
 <|> TYVAR <$> tyvar
 <|> bracket "function" "(function (types) type)"
                            (curry funtype <$> "(" >-- many ty --< ")" <*> ty)
 <|> badExpKeyword <$>! ("(" >-- @@ expKeyword <* scanToCloseParen)
 <|> curry CONAPP <$> "(" >-- ty <*> many ty --< ")" 
 <|> "(" >-- literal ")" <!> "empty type ()"
 <|> int     <!> "expected type; found integer"
 <|> booltok <!> "expected type; found Boolean literal"
) tokens
and badExpKeyword (loc, bad) =
      errorAt ("looking for type but found `" ^ bad ^ "'") loc

fun tyscheme tokens = (
     bracket "forall"    "(forall (tyvars) type)" 
                               (curry FORALL <$> "(" >-- forallNames --< ")" <*>
                                                                             ty)
 <|> curry FORALL [] <$> ty
) tokens
and forallNames ts = (
  nodups ("quantified type variable", "forall") <$>! @@ (many tyvar)
) ts
(* <parsing ((haskell))>=                       *)
fun define f formals body =
  nodups ("formal parameter", "definition of function " ^ f) formals >>=+
  (fn xs => DEFINE (f, (xs, body)))

val def = 
     bracket "define"  "(define f (args) body)" (define <$> name <*> @@ formals
                                                                        <*>!exp)
 <|> bracket "val"     "(val x e)"              (curry VAL    <$> name <*> exp)
 <|> bracket "val-rec" "(val-rec x e)"          (curry VALREC <$> name <*> exp)
 <|> bracket "vcon"    "(vcon C ty)"            (curry CONDEF <$> name <*>
                                                                       tyscheme)
 <|> bracket "use"     "(use filename)"         (USE          <$> name)
 <|> literal ")" <!> "unexpected right parenthesis"
 <|> EXP <$> exp
 <?> "definition"
(* <parsing ((haskell))>=                       *)
val haskellSyntax = (schemeToken, def)


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
(*   TYPE INFERENCE                                              *)
(*                                                               *)
(*****************************************************************)

(* Placeholder type checker                     *)
(*                                              *)
(* <type inference ((prototype))>=              *)
exception LeftAsExercise of string
(* <type inference ((haskell))>=                *)
fun typeof (e, Gamma) =
  let (* Calling typesof(<\ldotsne>, Gamma) returns (<\ldotsn *)
      (* tau>, \tyc) such that \typeisc\tyce_i tau_i for *)
      (* every i with 1<=i <=n. The base case is trivial; the *)
      (* induction step uses this rule from Section [->]:[*] \ *)
      (* usetyTypesOfC                                *)
      (* <function [[typesof]], to infer the types of a list of expressions ((ml
                                                                 /haskell))>= *)
      fun typesof ([],    Gamma) = ([], TRIVIAL)
        | typesof (e::es, Gamma) =
            let val (tau,  c)  = typeof  (e,  Gamma)
                val (taus, c') = typesof (es, Gamma)
            in  (tau :: taus, c /\ c')
            end
      (* Computing the type of a literal value is left as part *)
      (* of Exercise [->].                            *)
      (* <function [[literal]], to infer the type of a literal constant ((
                                                                prototype))>= *)
      fun literal _ = raise LeftAsExercise "literal"
      (* <function [[literal]], to infer the type of a literal constant ((
                                                                prototype))>= *)
      fun literal _ = (valtype, idsubst)
      (* <function [[ty]], to infer the type of an expression, given [[Gamma]] (
                                                               (prototype))>= *)
      fun addvar (x, g) = bindtyscheme (x, FORALL([], valtype), g)
      val valtyc = (valtype, TRIVIAL)
      fun ty (LITERAL v) = valtyc
        | ty (VAR x) = (findtyscheme (x, Gamma); valtyc)
        | ty (APPLY (e, es)) = check (e::es)
        | ty (LETX (LETSTAR, [], body)) = ty body
        | ty (LETX (LETSTAR, (b :: bs), body)) =
                         ty (LETX (LET, [b], LETX (LETSTAR, bs, body)))
        | ty (LETX (LET, bs, body)) =
             let val (xs, es) = ListPair.unzip bs
             in  ty (APPLY (LAMBDA (xs, body), es))
             end
        | ty (LETX (LETREC, bs, body)) =
             let val (xs, es) = ListPair.unzip bs
                 val Gamma' = foldl addvar Gamma xs
             in  (map (fn e => typeof(e, Gamma')) es; typeof(body, Gamma'))
             end
        | ty (DO (bs, body)) = ty (LETX (LETSTAR, bs, body))
        | ty (LAMBDA (xs, e)) = typeof(e, foldl addvar Gamma xs)
        | ty (IFX (e1, e2, e3)) =
             ty (CASE (e1, [(("#t", []), e2), (("#f", []), e3)]))
        | ty (CASE (e, matches)) =
             let val _ = map (matchtype (ty e)) matches
             in  valtyc
             end
      and check es = (map ty es; valtyc)
      and matchtype tau_case ((con, xs), e) = typeof (e, foldl addvar Gamma xs)
  in  ty e
  end


(*****************************************************************)
(*                                                               *)
(*   CHECKING AND EVALUATION                                     *)
(*                                                               *)
(*****************************************************************)

(* <checking and evaluation ((haskell))>=       *)
exception BugInTypeInference of string
(* <evaluation ((haskell))>=                    *)
(* Tracking lazy evaluation                     *)
(*                                              *)
(* To see what's happening, we can print the transitions *)
(* <definition of [[showforce]]>=               *)
(* Here's the printing code:                    *)
(* <definitions of [[expString]] and [[prenv]]>= *)
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
val rec expString = fn LITERAL v => valueString v
                     | VAR name => name
                     | APPLY (e, es) => prexps (e::es)
                     | LETX (lk, bs, e) => prWithBindings (prLetKind lk, bs, e)
                     | DO (bs, e) => prWithBindings ("do", bs, e)
                     | LAMBDA (xs, body) =>
                          "(lambda " ^ prnames xs ^ " " ^ expString body ^ ")"
                     | IFX (e1, e2, e3) => prexps [VAR "if", e1, e2, e3]
                     | CASE (e, ms) => foldl addMatch ("(case " ^ expString e)
                                                                              ms
and addMatch = fn ((m, b), pfx) => pfx ^ " (" ^ prApp m ^ " " ^ expString b ^
                                                                             ")"
and prApp = fn (c, []) => c
             | (c, xs) => prnames (c::xs)
and prexps  = fn l => "(" ^ spaceSep (map expString l) ^ ")"
and prnames = fn xs => "(" ^ spaceSep xs ^ ")"
and prWithBindings = fn (keyword, bs, e) =>
      "(" ^ keyword ^ " (" ^ prBindings bs ^ ") " ^ expString e ^ ")"
and prBindings = fn bs => separate ("", " ") (map prBinding bs)
and prBinding = fn (x, e) => "(" ^ x ^ " " ^ expString e ^ ")"
and prLetKind = fn LET => "let" | LETSTAR => "let*" | LETREC => "letrec"
val showingforce = ref false
val forceindent = ref 0
fun indent 0 = ()
  | indent n = (print "  "; indent (n-1))
fun startforce exp =
  if !showingforce then
     ( indent (!forceindent)
     ; app print ["Forcing <|", expString exp, ", rho|>\n"]
     ; forceindent := !forceindent + 1
     )
  else ()
    
fun showforce(exp, v) =
  if !showingforce then
     ( forceindent := !forceindent - 1
     ; indent (!forceindent)
     ; app print ["Forced <|", expString exp, ", rho|> to ", valueString  v,
                                                                           "\n"]
     )
  else ()
exception LeftAsExercise of string
exception BlackHole
fun force (ref (VALUE v)) = v
  | force (ref IN_PROGRESS) = raise BlackHole
  | force (thunk as ref (UNEVAL (exp, rho))) =
       let val () = thunk := IN_PROGRESS
           val () = startforce exp
           val v  = eval (exp, rho)
           val () = thunk := VALUE v
           val () = showforce (exp, v)
(* Forcing and evaluation                       *)
(*                                              *)
(* The hard part is getting from a thunk back to a weak *)
(* head normal form, which is done by evaluating *)
(* abstract syntax. The two are mutually recursive. *)
(* <boxed values 3>=                            *)
val _ = op eval  : thunk -> value
val _ = op force : loc   -> value
       in  v
       end
(* The [[BlackHole]] exception needs a handler. *)

(* Function [[eval]] forces a thunk. We show a couple of *)
(* simple cases: forcing a literal produces that *)
(* literal, and forcing a variable forces the location *)
(* the variable stands for. We also show one more *)
(* complex case: when forcing a [[case]] expression, we *)
(* insist that                                  *)
(*                                              *)
(*  1. The scrutinee must be a constructor application. *)
(*  2. There must be exactly exactly one case match *)
(*  which mentions the constructor being applied  *)
(*  ([[c]]).                                    *)
(*  3. The number of variables in the match must equal *)
(*  the number of arguments to the constructor. *)
(*                                              *)
(* <evaluation ((haskell))>=                    *)
and eval (e, rho) =
  let fun toThunk e = allocThunk (e, rho)
      fun ev (LITERAL v) = v
        | ev (VAR     x) = force (find (x, rho))
        | ev (CASE (e, arms)) =
            (case ev e
               of VCON (c, args) =>
                    (case List.filter (fn ((c', _), _) => c = c') arms
                       of [((_, formals), body)] =>
                            (eval(body, bindList (formals, args, rho))
                             handle BindListLength =>
                                 (* <bleat about [[c]] with [[args]] and
                                                                [[formals]]>= *)
                                 raise RuntimeError ("Constructor " ^ c ^
                                                            " was applied to " ^
                                                     Int.toString (length args)
                                          ^ " arguments, but case expression " ^
                                                     "expected " ^ Int.toString
                                              (length formals) ^ " arguments "))
                        | [] => raise RuntimeError ("Case expression had no " ^

                                              "alternative for constructor " ^ c
 ^ "; alternatives were: " ^ separate ("<none>", ", ") (map (fn ((c, _), _) => c
                                                                        ) arms))
                        | _ :: _ :: _ =>
                            raise RuntimeError ("Case expression had multiple "
                                                                               ^
                                                "alternatives for constructor "
                                                                            ^ c)
                    )
                | v => raise RuntimeError (
                                     "Case discrimination on non-constructor " ^
                                           valueString v)
             )
        (* Monadic primitives and [[do]] notation       *)
        (*                                              *)
        (* <cases for evaluation of [[do]] notation>=   *)
        | ev (DO ([], body)) = ev body
        | ev (DO ((x, e) :: bindings, body)) =
           ev (APPLY (LITERAL (PRIMITIVE monadicBindList),
                      [e, LAMBDA([x], DO (bindings, body))]))
        (* Forcing other kinds of thunks is \exref      *)
        (* haskell.ex.eval.                             *)
        (* <other cases for internal function [[ev]] ((prototype))>= *)
        | ev _ = raise LeftAsExercise "evaluating thunks"
  in  ev e
  end
(* <[[and]] definitions of monadic functions>=  *)
and monadicBind (mLoc, kLoc) =
  IO (fn () => let val a = runIO (force mLoc)
               in  runIO (force (apply (kLoc, [a])))
               end)
and runIO (IO f) = f ()
  | runIO _      = raise BugInTypeInference "expected I/O action"
and apply (f, args) =
  allocThunk (APPLY (LITERAL (force f), map (LITERAL o force) args), emptyEnv)
and monadicBindList [m, k] = monadicBind (m, k)
  | monadicBindList _ = let exception ThisCan'tHappen in raise ThisCan'tHappen
                                                                             end
(* <evaluation ((haskell))>=                    *)
fun fullyEval v =
  let fun full (VCON (c, args)) = app (full o force) args
        | full (NUM n)       = ()
        | full (SYM v)       = ()
        | full (CLOSURE   _) = ()
        | full (PRIMITIVE _) = ()
        | full (IO _       ) = ()
      val _ = full v
(* The full primitive                           *)
(*                                              *)
(* <boxed values 4>=                            *)
val _ = op fullyEval : value -> value
  in  v
  end
(* <evaluation ((haskell))>=                    *)
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

fun evaldef (d, rho : loc env) =
  let 
(* <boxed values 8>=                            *)
val _ = op evaldef : def * loc env -> loc env * string
  in  case d
        of VALREC (name, e)      => let val cell = ref IN_PROGRESS
                                        val rho  = bind (name, cell, rho)
                                        val _    = cell := UNEVAL (e, rho)
                                    in  (rho, locString cell)
                                    end
         | VAL    (name, e)      => let val cell = ref IN_PROGRESS
                                        val _    = cell := UNEVAL (e, rho)
                                        val rho  = bind (name, cell, rho)
                                    in  (rho, locString cell)
                                    end
         | EXP e                 => (* <evaluate [[e]] and run or bind the
                                                                     result>= *)
                                    (case eval (e, rho)
                                       of IO action => (action () ; (rho, ""))
                                        | v => let val cell = allocValue v
                                               in  (bind ("it", cell, rho),
                                                                 locString cell)
                                               end)
         | DEFINE (name, lambda) => evaldef (VALREC (name, LAMBDA lambda), rho)
         | CONDEF (name, ty)     => let val cell = allocValue (vconValue (name,
                                                                            ty))
                                        val rho  = bind (name, cell, rho)
                                    in  (rho, name)
                                    end
         | USE _ => raise RuntimeError "internal error -- USE reached evaldef"
  end
and vconValue (name, sigma) =
  if takesArgs sigma then
    PRIMITIVE (fn args => VCON (name, args))
  else
    VCON (name, [])
and takesArgs (FORALL (_, CONAPP (TYCON "function", _))) = true
  | takesArgs (FORALL (_, _))                            = false
(* <evaluation ((haskell))>=                    *)
fun elabdef (d, Gamma) =
  case d
    of VALREC (x, e)      => (* The code for [[VALREC]] is a bit more
                                                                 complicated. *)
                             (* We need an environment that binds x to tau, but
                                                                           we *)
                             (* don't yet know tau. The original rule looks like
                                                                              *)
                             (* this: \usetyValRec Here's a version with
                                                                 constraints: *)
                             (* \tyrule[ValRecC]ValRec \upshapewith constraints
                                                                            \ *)
                             (* threeline \typeisc[{x |->alpha}] \tyce tau\
                                                                   qquadalpha *)
                             (* is fresh \twoquad\trivsat\subsn(\tyc\landalpha\
                                                                         eqty *)
                             (* tau) \subsnGamma=Gamma sigma= \generalize\
                                                                   subsnalpha *)
                             (* \ftv(Gamma) \topt\xvalrec(x, e) -->Gamma{x |->
                                                                       sigma} *)
                             (*                                              *)
                             (* As usual, we introduce a fresh type variable to
                                                                        stand *)
                             (* for tau, then constrain it to be equal to the
                                                                         type *)
                             (* of e.                                        *)
                             (* <infer and bind type for [[VALREC (x, e)]]>= *)
                             let val alpha    = freshtyvar ()
                                 val Gamma'   = bindtyscheme (x, FORALL ([],
                                                                  alpha), Gamma)
                                 val (tau, c) = typeof (e, Gamma')
                                 val theta    = solve (c /\ alpha =*= tau)
                                 val sigma    = generalize (tysubst theta alpha,
                                                          freetyvarsGamma Gamma)
                             in  (bindtyscheme (x, sigma, Gamma),
                                                         typeSchemeString sigma)
                             end
     | VAL    (x, e)      => (* The cases for [[VAL]] and [[VALREC]] resemble
                                                                         each *)
                             (* other. We begin with [[VAL]], which computes a
                                                                         type *)
                             (* and generalizes it. \usetyValC               *)
                             (* <infer and bind type for [[VAL    (x, e)]]>= *)
                             let val (tau, c) = typeof (e, Gamma)
                                 val theta    = solve c
                                 val sigma    = generalize (tysubst theta tau,
                                                          freetyvarsGamma Gamma)
                             in  (bindtyscheme (x, sigma, Gamma),
                                                         typeSchemeString sigma)
                             end
                             (* This code takes a big shortcut: we just assume
                                                                       that \ *)
                             (* subsnGamma=Gamma. How can we get away with this
                                                                              *)
                             (* assumption? Because we can prove that a top-
                                                                       level  *)
                             (* Gamma never contains a free type variable. This
                                                                              *)
                             (* property guarantees that \subsnGamma=Gamma for
                                                                        any \ *)
                             (* subsn. You can prove this property for yourself
                                                                         in \ *)
                             (* exrefpageml.ex.no-free-tyvars-at-top-level.  *)

     | EXP e              => (* <infer and bind type for [[EXP e]] ((haskell))>=
                                                                              *)
                             let val (tau, c) = typeof (e, Gamma)
                                 val theta    = solve c
                                 val sigma    = generalize (tysubst theta tau,
                                                          freetyvarsGamma Gamma)
                             in  (bindtyscheme ("it", sigma, Gamma),
                                                         typeSchemeString sigma)
                             end
     | DEFINE (x, lambda) => elabdef (VALREC (x, LAMBDA lambda), Gamma)
     | CONDEF (c, sigma)  => (* <bind constructor [[c]] to type [[sigma]]>=  *)
                             (* XXX missing kind check on sigma *)
                             (bindtyscheme (c, sigma, Gamma), typeSchemeString
                                                                          sigma)
                             (* Complete implementation of micro-Haskell     *)
                             (*                                              *)
                             (* [*] This Appendix presents the solutions to some
                                                                           of *)
                             (* the implementation problems in Chapter [->]. *)

     | USE filename       => raise RuntimeError 
                                     "internal error -- `use' reached elabdef"
type env_bundle = type_env * loc env
fun elabEvalDef (d, envs as (Gamma, rho), echo) =
  case d
    of USE filename => use readCheckEvalPrint haskellSyntax filename envs
     | _ =>
        let val (Gamma, tystring)  = elabdef (d, Gamma)
            val (rho,   valstring) = evaldef (d, rho)
            val _ = if size valstring > 0 then echo (valstring ^ " : " ^
                                                                       tystring)
                    else ()
(* <boxed values 9>=                            *)
val _ = op elabEvalDef : def * env_bundle * (string -> unit) -> env_bundle
        in  (Gamma, rho)
        end
(* As in Typed uScheme, [[elabEvalDef]] preserves the *)
(* phase distinction: type inference is independent of *)
(* [[rho]] and [[evaldef]].                     *)

(* <checking and evaluation ((haskell))>=       *)
and readCheckEvalPrint (defs, echo, errmsg) envs =
  let fun process (def, envs) =
        let fun continue msg = (errmsg msg; envs)
        in  elabEvalDef (def, envs, echo)
            handle IO.Io {name, ...} => continue ("I/O error: " ^ name)
            (* <more read-eval-print handlers>=             *)
            | BlackHole => continue "error: evaluation hit a black hole"
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

            (* <more read-eval-print handlers>=             *)
            | TypeError          msg => continue ("type error: " ^ msg)
            | BugInTypeInference msg => continue ("bug in type inference: " ^
                                                                            msg)
        end
  in  streamFold process envs defs
  end
(* The read-eval-print loop                     *)
(*                                              *)
(* The read-eval-print loop almost identical to the *)
(* read-eval-print loop for Typed uScheme; the only *)
(* difference is that instead of [[BugInTypeChecking]], *)
(* we have and [[BugInTypeInference]].          *)
(* <boxed values 10>=                           *)
val _ = op readCheckEvalPrint : def stream * (string->unit) * (string->unit) ->
                                                        env_bundle -> env_bundle


(*****************************************************************)
(*                                                               *)
(*   PRIMITIVES                                                  *)
(*                                                               *)
(*****************************************************************)

(* <primitives ((haskell))>=                    *)
fun strict f = f o map force
fun arityError n args =
  raise RuntimeError ("primitive function expected " ^ Int.toString n ^
                      "arguments; got " ^ Int.toString (length args))
fun binary_valop f = strict (fn [a, b] => f(a, b) | args => arityError 2 args)
fun unary_valop  f = strict (fn [a]    => f a     | args => arityError 1 args)
(* Primitives                                   *)
(*                                              *)
(* The distinction between strict and non-strict primops *)
(* returns! But the semantics is slightly different this *)
(* time?environment are never involved. [[cons]] is the *)
(* only non-strict primop.                      *)
(* <boxed values 5>=                            *)
val _ = op strict : (value list -> value) -> primitive
val _ = op unary_valop : (value -> value) -> primitive
(* Arithmetic primitives expect and return integers. *)
(* <primitives ((haskell))>=                    *)
fun arithop f = binary_valop (fn (NUM n1, NUM n2) => NUM (f (n1, n2))
                               | _ => raise RuntimeError "integers expected")
val arithtype    = funtype ([inttype, inttype], inttype)
fun comptype tau = funtype ([tau, tau], booltype)
(* We use the chunk [[<<primitives [[::]]       *)
(* ((haskell))>>]] to cons up all the primitives and *)
(* their names into one giant list. [One advantage of *)
(* literate programming is we can distribute this *)
(* definition throughout the source file, so we can put *)
(* the parts where they make the most sense. In this *)
(* case, we put the pieces of the list of primitives *)
(* near those higher-order functions we use to define *)
(* them.] We'll use that list to build the initial *)
(* environment for the read-eval-print loop.    *)

(* <primitives ((haskell))>=                    *)
fun inject_bool x =
      VCON (if x then "#t" else "#f", [])
fun project_bool (VCON ("#t", [])) = true
  | project_bool (VCON ("#f", [])) = false
  | project_bool _ = raise RuntimeError "projected non-boolean"

fun inject_predicate f = fn x => inject_bool (f x)
fun predop f = unary_valop  (inject_predicate f)

fun comparison f = binary_valop (inject_predicate f)
fun intcompare f = comparison (
                     fn (NUM n1, NUM n2) => f (n1, n2)
                      | _ => raise BugInTypeInference "integers expected")
(* We have two kinds of predicates: ordinary predicates *)
(* take one argument, and comparisons take two. Some *)
(* comparisons apply only to integers. (From here on, *)
(* you can figure out the types for yourself?or get the *)
(* ML compiler to tell you.)                    *)
(* <boxed values 6>=                            *)
val _ = op inject_bool  : bool -> value
val _ = op project_bool : value -> bool
(* And here come the predicates. Equality comparison *)
(* succeeds only on symbols and numbers. The empty list *)
(* is dealt with through [[case]] expressions.  *)

(* The list primitives are dead easy, except we have to *)
(* deal with non-strictness and forcing.        *)
(* <primitives ((haskell))>=                    *)
fun ns_unary  f = (fn [a]    => f a      | args => arityError 1 args)
fun ns_binary f = (fn [a, b] => f (a, b) | args => arityError 2 args)
(* <primitives ((haskell))>=                    *)
val unitval   = VCON ("unit", [])
val unitthunk = allocValue unitval
(* Monadic primitives                           *)
(*                                              *)
(* <boxed values 7>=                            *)
val _ = op apply : loc * loc list -> loc
val _ = op monadicBind : loc * loc -> value


(*****************************************************************)
(*                                                               *)
(*   INITIALIZATION                                              *)
(*                                                               *)
(*****************************************************************)

(* <initialization ((haskell))>=                *)
val initialEnvs =
  let fun addPrim ((name, prim, tau), (Gamma, rho)) = 
        ( bindtyscheme (name, generalize (tau, freetyvarsGamma Gamma), Gamma)
        , bind (name, allocValue (PRIMITIVE prim), rho)
        )
      val envs  = foldl addPrim (emptyTypeEnv, emptyEnv) ((* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("full", unary_valop
                                         fullyEval, funtype ([alpha], alpha)) ::
                                                          (* Here's a primitive
                                                to determined whether we show *)
                                                          (* forces:
                                                                              *)
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ( "showforce"
                                                          , unary_valop (fn x =>
                                            (showingforce := project_bool x; x))
                                                          , funtype ([booltype],
                                                                       unittype)
                                                          ) ::
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("+", arithop op +,
                                                                   arithtype) ::
                                                          ("-", arithop op -,
                                                                   arithtype) ::
                                                          ("*", arithop op * ,
                                                                   arithtype) ::
                                                          ("/", arithop op div,
                                                                   arithtype) ::
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("<", intcompare op <,
                                                            comptype inttype) ::
                                                          (">", intcompare op >,
                                                            comptype inttype) ::
                                                          ("=", comparison (fn (
                                                      NUM n1, NUM n2) => n1 = n2
                                                                             | (
                                                      SYM v1, SYM v2) => v1 = v2
                                                                             |
                      _ => raise RuntimeError "equality used on non-base type"),
                                                                comptype alpha)
                                                                              ::
                                                          (*
                                                          ("number?",  predop (
                                           fn (NUM  _) => true | _ => false)) ::
                                                          ("symbol?",  predop (
                                           fn (SYM  _) => true | _ => false)) ::
                                                          *)
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("error", unary_valop
                       (fn v => raise RuntimeError (valueString (fullyEval v))),
                                                                      funtype ([
                                                               alpha], beta)) ::
                                                          ("show", unary_valop (
                                                             SYM o valueString),
                                                                    funtype ([
                                                            alpha], symtype)) ::
                                                          ("symwidth",
                                         unary_valop (fn (SYM s) => NUM (size s)

                     | _ => raise BugInTypeInference "symwidth got non-symbol"),
                                                                    funtype ([
                                                          symtype], inttype)) ::
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("cons", ns_binary (fn
                                                (a, b) => VCON("cons", [a, b])),

                           funtype ([alpha, listtype alpha], listtype alpha)) ::
                                                          (* ("tuple", fn es =>
                                                       VCON ("tuple", es)) :: *)
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("trace", let fun
                                       bleat s = TextIO.output(TextIO.stdErr, s)
                                                                    in
                                                       ns_binary (fn (msg, v) =>

                                                      (app bleat ["**TRACE**: ",

                                      valueString (fullyEval (force msg)), "\n"]

                                                                     ; force v))
                                                                    end,

                                               funtype ([alpha, beta], beta)) ::
                                                          (* <primitives [[::]]
                                                    ((haskell))>=             *)
                                                          ("print", unary_valop
                (fn v => IO (fn () => ( print (valueString (fullyEval v) ^ "\n")

                                                                 ; unitthunk))),
                                                                    funtype ([
                                                    alpha], iotype unittype)) ::
                                                          ("return", ns_unary (
                                               fn thunk => IO (fn () => thunk)),
                                                                    funtype ([
                                                       alpha], iotype alpha)) ::
                                                          (">>=", ns_binary
                                                                    monadicBind,
                                                                    funtype ([
            iotype alpha, funtype ([alpha], iotype beta)], iotype beta)) :: nil)
      val basis  = (* <ML representation of initial basis>=        *)

                    [ "(define map (f xs)"
                    , "  (case xs"
                    , "     (() '())"
                    , "     ((cons y ys) (cons (f y) (map f ys)))))"
                    ,
                  "(vcon pair (forall ('a 'b) (function ('a 'b) (pair 'a 'b))))"
                    , "(define fst (p)"
                    , "   (case p ((pair x y) x)))"
                    , "(define snd (p)"
                    , "   (case p ((pair x y) y)))"
                    , "(define list1 (x) (cons x '()))"
                    , "(define bind (x y alist)"
                    , "  (case alist"
                    , "       (() (list1 (pair x y)))"
                    , "       ((cons p ps)"
                    , "          (if (= x (fst p))"
                    , "              (cons (pair x y) ps)"
                    , "              (cons p (bind x y ps))))))"
                    , "(define null? (xs)"
                    , "   (case xs (() #t)"
                    , "            ((cons y ys) #f)))"
                    , "(define car (xs)"
                    , "   (case xs (() (error 'car-of-empty-list))"
                    , "            ((cons x _) x)))"
                    , "(define cdr (xs)"
                    , "   (case xs (() (error 'cdr-of-empty-list))"
                    , "            ((cons _ xs) xs)))"
                    , "(define isbound? (x alist)"
                    , "  (if (null? alist) "
                    , "    #f"
                    , "    (if (= x (fst (car alist)))"
                    , "      #t"
                    , "      (isbound? x (cdr alist)))))"
                    , "(define find (x alist)"
                    , "  (if (null? alist) "
                    , "    (error 'not-found)"
                    , "    (if (= x (fst (car alist)))"
                    , "      (snd (car alist))"
                    , "      (find x (cdr alist)))))"
                    , "(vcon unit unit)"
                    , "(define >> (m1 m2) (>>= m1 (lambda (_) m2)))"
                    , "(define mapM_ (f xs)"
                    , "  (case xs (() (return unit))"
                    , "           ((cons y ys) (>> (f y) (mapM_ f ys)))))"
                    , "(vcon some (forall ('a) (function ('a) (option 'a))))"
                    , "(vcon none (forall ('a) (option 'a)))"
                    , "(define tails (xs)"
                    , "  (cons xs (if (null? xs) '() (tails (cdr xs)))))"
                    , "(define caar (xs) (car (car xs)))"
                    , "(define cadr (xs) (car (cdr xs)))"
                    , "(define cdar (xs) (cdr (car xs)))"
                    , "(define cddr (xs) (cdr (cdr xs)))"
                    , "(define cdddr (xs) (cdr (cddr xs)))"
                    , "(define length (xs)"
                    , "  (if (null? xs) 0"
                    , "    (+ 1 (length (cdr xs)))))"
                    , "(define and (b c) (if b  c  b))"
                    , "(define or  (b c) (if b  b  c))"
                    , "(define not (b)   (if b #f #t))"
                    , "(define append (xs ys)"
                    , "  (if (null? xs)"
                    , "     ys"
                    , "     (cons (car xs) (append (cdr xs) ys))))"
                    , "(define revapp (xs ys)"
                    , "  (if (null? xs)"
                    , "     ys"
                    , "     (revapp (cdr xs) (cons (car xs) ys))))"
                    , "(define reverse (xs) (revapp xs '()))"
                    , "(define o (f g) (lambda (x) (f (g x))))"
                    , "(define curry   (f) (lambda (x) (lambda (y) (f x y))))"
                    , "(define uncurry (f) (lambda (x y) ((f x) y)))"
                    , "(define filter (p? l)"
                    , "  (if (null? l)"
                    , "    '()"
                    , "    (if (p? (car l))"
                    , "      (cons (car l) (filter p? (cdr l)))"
                    , "      (filter p? (cdr l)))))"
                    , "(define exists? (p? l)"
                    , "  (if (null? l)"
                    , "    #f"
                    , "    (if (p? (car l)) "
                    , "      #t"
                    , "      (exists? p? (cdr l)))))"
                    , "(define all? (p? l)"
                    , "  (if (null? l)"
                    , "    #t"
                    , "    (if (p? (car l))"
                    , "      (all? p? (cdr l))"
                    , "      #f)))"
                    , "(define foldr (op zero l)"
                    , "  (if (null? l)"
                    , "    zero"
                    , "    (op (car l) (foldr op zero (cdr l)))))"
                    , "(define foldl (op zero l)"
                    , "  (if (null? l)"
                    , "    zero"
                    , "    (foldl op (op (car l) zero) (cdr l))))"
                    , "(define <= (x y) (not (> x y)))"
                    , "(define >= (x y) (not (< x y)))"
                    , "(define != (x y) (not (= x y)))"
                    , "(define max (x y) (if (> x y) x y))"
                    , "(define min (x y) (if (< x y) x y))"
                    , "(define mod (m n) (- m (* n (/ m n))))"
                    , "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))"
                    , "(define lcm (m n) (* m (/ n (gcd m n))))"
                    , "(define min* (l) (foldr min (car l) (cdr l)))"
                    , "(define max* (l) (foldr max (car l) (cdr l)))"
                    , "(define gcd* (l) (foldr gcd (car l) (cdr l)))"
                    , "(define lcm* (l) (foldr lcm (car l) (cdr l)))"
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
                    , "(define takewhile (p? l)"
                    , "  (if (null? l)"
                    , "     '()"
                    , "     (if (p? (car l))"
                    , "         (cons (car l) (takewhile p? (cdr l)))"
                    , "         '())))"
                    , "(define dropwhile (p? l)"
                    , "  (if (null? l)"
                    , "     '()"
                    , "     (if (p? (car l))"
                    , "         (dropwhile p? (cdr l))"
                    , "         l)))"
                    , "(define drop (n l)"
                    , "  (if (null? l)"
                    , "     '()"
                    , "     (if (= n 0)"
                    , "         l"
                    , "         (drop (- n 1) (cdr l)))))"
                    , "(define nth (xs n)"
                    , "   (car (drop n xs)))"
                    , "(define take (n xs)"
                    , "  (if (or (= n 0) (null? xs))"
                    , "      '()"
                    , "      (cons (car xs) (take (- n 1) (cdr xs)))))"
                     ]
      fun writeln s = app print [s, "\n"]
      fun bleat s = TextIO.output(TextIO.stdErr, s ^ "\n")
      val defs  = reader haskellSyntax noPrompts ("initial basis", streamOfList
                                                                          basis)
  in  readCheckEvalPrint (defs, fn _ => (), bleat) envs
  end
(* <initialization ((haskell))>=                *)
fun runInterpreter noisy = 
  let val rho = initialEnvs
      fun writeln s = app print [s, "\n"]
      fun errorln s = TextIO.output (TextIO.stdErr, s ^ "\n")
      val prompts = if noisy then stdPrompts else noPrompts
      val defs =
        reader haskellSyntax prompts ("standard input", streamOfLines
                                                                   TextIO.stdIn)
  in  ignore (readCheckEvalPrint (defs, writeln, errorln) rho)
  end 
(* The function [[runInterpreter]] takes one argument, *)
(* which tells it whether to prompt. It reads from *)
(* standard input.                              *)
(* <boxed values 11>=                           *)
val _ = op runInterpreter : bool -> unit
(* Within the read-eval-print loop, [[writeln]] acts as *)
(* both the [[echo]] and the [[errmsg]] functions. *)
(*                                              *)



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
