(* 1   *)
(* 1 a *)
fun fib (0 : int) : int = 0
  | fib (1 : int) : int = 1
  | fib (n : int) : int = fib(n - 1) + fib(n - 2);

fun fib 0 = 0
  | fib 1 = 1
  | fib n = fib(n - 1) + fib(n - 2);


(* 1 b *)
fun firstVowel (x::_) = Char.contains "aeiou" x
  | firstVowel (_)    = false;


(* 1 c *)
fun null ([])   = true
  | null (_::_) = false;


(* 2   *)
(* 2 a *)
fun rev xs = foldr  (fn (x, xs) => xs @ [x]) [] xs;


(* 2 b *)
fun minList [] = raise Match
  | minList xs = foldr (fn (a, b) => if a < b then a else b) (valOf Int.maxInt) xs;


(* 2 c *)
fun foldl f z []      = z
  | foldl f z (x::xs) = foldl f (f (z, x)) xs;

fun foldr f z []      = z
  | foldr f z (x::xs) = f (x, foldr f z xs);


(* 2 d *)
exception Mismatch;

fun zip ((x::xs), (y::ys)) = (x, y)::zip(xs, ys)
  | zip ([], []) = []
  | zip (_, _)  = raise Mismatch;


(* 2 e *)
fun pairfoldr f z ((x::xs), (y::ys)) = f (x, y, pairfoldr f z (xs, ys))
  | pairfoldr f z (_,  _) = z;

fun zip2 (xs, ys) = pairfoldr (fn (x, y, z) => (x, y)::z) [] (xs, ys);


(* 2 f *)
fun unzip (xys : ('a * 'b) list) =  let
  fun unzipper (xs, ys) ((x, y)::xys) = unzipper (xs @ [x], ys @ [y]) xys
    | unzipper (xs, ys ) []  = (xs, ys)
  in unzipper ([], []) xys end;


(* 2 g *)
fun flatten [] = []
  | flatten (x::xs) = x @ flatten xs;


(* 3 *)
(* 3 a *)
exception InvalidIndex;

fun nth 0         (x::xs)           = x
  | nth (n : int) (x::xs : 'a list) = nth (n - 1) xs
  | nth _         []                = raise InvalidIndex;


(* 3 b *)
exception NotFound of string;

type 'a env = (string * 'a) list;

val emptyEnv : 'a env = []

val bindVar : string * 'a * 'a env -> 'a env =
  fn (varName, value, env) => (varName, value)::env;

val rec lookup : string * 'a env -> 'a =
  fn (varName, (name, value)::env) => if varName = name then value 
                                      else lookup(varName, env)
   | (varName, [])                 => raise NotFound(varName);

(*
type 'a env = string -> 'a
val emptyEnv = []
fun lookup (name, rho) = rho name;
  *)

val isBound : string * 'a env -> bool = 
  fn (str, env) => if lookup (str, env) then true
    handle NotFound(str) => false;


(* 4 *)
(* 4 a *)
datatype 'a tree = NODE of 'a tree * 'a * 'a tree
                 | LEAF

fun insert cmp = let 
  fun ins (x, LEAF) = NODE (LEAF, x, LEAF)
    | ins (x, NODE (left, y, right)) =
        (case cmp (x, y)
          of LESS    => NODE (ins (x, left), y, right)
           | GREATER => NODE (left, y, ins (x, right))
           | EQUAL   => NODE (left, x, right))
  in ins
end;

fun intOrder (a, b) = 
  if a < b then LESS 
  else if a > b then GREATER 
  else EQUAL;

datatype 'a set = SET of ('a * 'a -> order) * 'a tree;
fun nullset cmp = SET (cmp, LEAF);

 (* 
val addelt : 'a * 'a set -> 'a set = 
  fn (elem, set) | 
    *)
