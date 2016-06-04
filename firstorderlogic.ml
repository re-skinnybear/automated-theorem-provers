(*  COMP 560-2 First Order Logic and Shared Functions
*   Theodore (Ted) Kim
*)

module FOL = struct

type term =
    TVar of string
  | TFunction of string * int * term list

type formula =
    FTruth
  | FFalsity
  | FConj of formula * formula
  | FDisj of formula * formula
  | FImp of formula * formula
  | FNeg of formula
  | FForall of string * formula
  | FExists of string * formula
  | FRel of string * int * term list

type constr = term * term
type constraints = constr list

type substitution = (string * term) list

(* Predicate symbol *)
let pSym (s : string) : formula = FRel (s, 0, [])

(* Error for cases that should never happen *)
exception SOMETHINGWENTWRONG
exception CONFLICT
exception OCCURRENCE

(* Pretty printing *)
let rec intersperse (sep : 'a) (xs : 'a list) : 'a list =
  match xs with
    []        -> []
  | (x :: []) -> x :: []
  | (x :: xs) -> x :: sep :: intersperse sep xs

let rec showTerm (t : term) : string =
  match t with
    TVar s -> s
  | TFunction(f, _, xs) ->
      f ^ "(" ^ (String.concat "" (intersperse "," (List.map showTerm xs))) ^ ")"

let rec show (x : formula) : string =
  match x with
    FTruth -> "⊤"
  | FFalsity -> "⊥"
  | FConj(y, z) -> "(" ^ show y ^ " ∧ " ^ show z ^ ")"
  | FDisj(y, z) -> "(" ^ show y ^ " ∨ " ^ show z ^ ")"
  | FImp(y, z) -> "(" ^ show y ^ " → " ^ show z ^ ")"
  | FNeg y -> "(" ^ "¬" ^ show y ^ ")"
  | FForall(var, y) -> "∀" ^ var ^ ". " ^ "(" ^ show y ^ ")"
  | FExists(var, y) -> "∃" ^ var ^ ". " ^ "(" ^ show y ^ ")"
  | FRel(name, 0, []) -> name
  | FRel(name, _, xs) ->
      name ^ "(" ^ (String.concat "" (intersperse "," (List.map showTerm xs))) ^ ")"

let printFormula (x : formula) : unit = (print_string (show x); print_string "\n")

let rec showTerm (t : term) : string =
  match t with
    TVar s -> s
  | TFunction(f, _, xs) ->
      f ^ "(" ^ (String.concat "" (intersperse "," (List.map showTerm xs))) ^ ")"

let showTerms (y, z : term * term) : string =
  (showTerm y) ^ " = " ^ (showTerm z)

let showConstraints (xs : constraints) : string =
  "<" ^ (String.concat "" (intersperse "," (List.map showTerms xs))) ^ ">"

let printConstraints (x : constraints) : unit = (print_string (showConstraints x); print_string "\n")

end