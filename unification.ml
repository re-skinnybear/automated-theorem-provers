(*  COMP 560-2 Unification Solver
*   Theodore (Ted) Kim
*)

module UNIFY = struct
open FOL

let rec occurs_free (x : string) (t2 : term) : bool =
  match t2 with
  | TVar y -> x = y
  | TFunction(c, 0, xs) -> false
  | TFunction (f, _, xs) ->
        List.fold_left (fun b z -> occurs_free x z ||b) false xs
  | _ -> raise SOMETHINGWENTWRONG

(* Assumes lists are of equal length *)
let rec zip lst1 lst2 = 
  match lst1,lst2 with
    [], [] -> []
  | (x::xs),(y::ys) -> (x,y) :: (zip xs ys)
  | _ -> raise SOMETHINGWENTWRONG

let rec subst (s : substitution) (t : term) : term =
  match t with
  | TVar x -> if List.mem_assoc x s then List.assoc x s else TVar x
  | TFunction (f, fa, ftms) ->
      TFunction (f, fa, List.map (fun x -> subst s x) ftms)

(* Substitution applied to a constraint *)
let substConstraint (s : substitution) (y, z : constr) : constr =
  subst s y, subst s z

(* Substitution applied to constraints *)
let apply_subst (s : substitution) (xs : constraints) : constraints =
  List.map (fun x -> substConstraint s x) xs

let rec remove_dupes lst = 
  match lst with 
    [] -> []
  | x::xs -> x::(remove_dupes (List.filter (fun y -> y<>x) xs))

let compose_subst (g : substitution) (f : substitution) : substitution =
  let f' = List.filter (fun (x',t') -> not (List.mem_assoc x' g)) f
  in let fg = (List.map (fun (x',t') -> (x', subst f t')) g) @ f'
  in remove_dupes fg

let applyRules (y, z : constr) (xs : constraints) (s : substitution) : constraints * substitution =
  (* Erasing *)
  if y = z
  then xs, s
  else
  match y, z with
    TFunction(f, fa, ftms), TFunction(g, ga, gtms) ->
      if f <> g || fa <> ga
      (* Conflict *)
      then raise CONFLICT
      (* Decomposition *)
      else zip ftms gtms @ xs, s
  | TVar x, z ->
      if occurs_free x z
      (* Occurrence *)
      then raise OCCURRENCE
      (* Elimination *)
      else let s' = (x, z)
      in apply_subst [s'] xs, compose_subst s [s']
      (* Inversion *)
  | y, TVar x -> (TVar x, y)::xs, s

let rec applyUnification (x : constraints) (s : substitution) : substitution =
  match x with
    [] -> s
  | (x::xs) -> let (xs', s') = applyRules x xs s
               in applyUnification xs' s'

(* Pretty printing for substitutions *)
let rec print_subst (s : substitution) : string =
  match s with
  | [] -> ""
  | [(x,t)] -> showTerm(t)^"/"^x
  | (x,t)::xs -> showTerm(t)^"/"^x^","^(print_subst xs)

let printSubstitution (x : substitution) : unit = (print_string ("{"^(print_subst x)^"}"); print_string "\n")

let unify (x : constraints) : substitution =
  applyUnification x []

(* Tests *)
let e1 = [(TVar "X", TFunction("f", 1, [TVar "Y"]))]
let e2 = [
(TFunction("f", 2, [TVar "X"; TFunction("c", 0, [])]),
TFunction("f", 2, [TFunction("c", 0, []); TVar "X"]));
(TFunction("g", 2, [TFunction("d", 0, []); TVar "X1"]),
TFunction("g", 2, [TVar "X2"; TVar "X3"]));
(TFunction("h", 1, [TVar "X2"]), TFunction("c", 0, []))
]
let e3 = [(TFunction("a", 0, []),TFunction("a", 0, []))]
let e4 = [(TVar "X", TVar "X")]
let e5 = [(TFunction("a", 0, []), TVar "X")]
let e6 = [(TFunction("a", 0, []),TFunction("b", 0, []))]
let e7 = [(TVar "X", TVar "Y")]
let e8 = [(TFunction("f", 2, [TFunction("a", 0, []); TVar "X"]),
  TFunction("f", 2, [TFunction("a", 0, []); TFunction("b", 0, [])]))]
let e9 = [(TFunction("f", 1, [TFunction("a", 0, [])]),
TFunction("g", 1, [TFunction("a", 0, [])]))]
let e10 = [(TFunction("f", 1, [TVar "X"]),
TFunction("f", 1, [TVar "Y"]))]
let e11 = [(TFunction("f", 1, [TFunction("g", 1, [TVar "X"])]),
TFunction("f", 1, [TVar "Y"]))]
let e12 = [(TFunction("f", 1, [TFunction("g", 1, [TVar "X"]); TVar "X"]),
TFunction("f", 1, [TVar "Y"; TFunction("a", 0, [])]))]
let e13 = [(TVar "X", TVar "Y"); (TVar "Y", TFunction("a", 0, []))]
let e14 = [(TVar "X", TFunction("a", 0, [])); (TFunction("b", 0, []), TVar "X")]

end