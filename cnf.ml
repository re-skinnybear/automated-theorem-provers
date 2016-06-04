(*  COMP 560-2 Conjunctive Normal Form Converter
*   Theodore (Ted) Kim
*)

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

exception SOMETHINGWENTWRONG

let pSym (s : string) : formula = FRel (s, 0, [])

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

let applyToSubformula (f : formula -> formula) (x : formula) : formula =
  match x with
    FConj(y, z) -> FConj (f y, f z)
  | FDisj(y, z) -> FDisj (f y, f z)
  | FImp(y, z) -> FImp (f y, f z)
  | FNeg y -> FNeg (f y)
  | FForall(var, y) -> FForall (var, f y)
  | FExists(var, y) -> FExists (var, f y)
  | _ -> x

let rec isQuantifierFree (x : formula) : bool =
  match x with
    FConj(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FDisj(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FImp(y, z) -> isQuantifierFree y && isQuantifierFree z
  | FNeg y -> isQuantifierFree y
  | FForall(var, y) -> false
  | FExists(var, y) -> false
  | _ -> true

let rec isPrenex (x : formula) : bool =
  match x with
    FForall(_, y) -> isPrenex y
  | FExists(_, y) -> isPrenex y
  | _ -> isQuantifierFree x

let freshCount : int ref = ref 0

let rec renameTerm (x : term) (old : string) (fresh : string) : term =
  match x with
    TVar s -> TVar (if s = old then fresh else s)
  | TFunction(name, a, xs) ->
      TFunction(name, a, List.map (fun t -> (renameTerm t old fresh)) xs)

let rec renameFormula (x : formula) (old : string) (fresh : string) : formula =
  match x with
    FForall(var, y) ->
      if var = old then x else FForall(var, renameFormula y old fresh)
  | FExists(var, y) ->
      if var = old then x else FExists(var, renameFormula y old fresh)
  | FRel(name, a, xs) ->
      FRel(name, a, List.map (fun t -> renameTerm t old fresh) xs)
  | _ -> applyToSubformula (fun y -> renameFormula y old fresh) x

let rec renameBoundedVars (x : formula) : formula =
  match x with
    FForall(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = "_" ^ string_of_int (!freshCount)
      in FForall(fresh, renameFormula y var fresh)
  | FExists(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = "_" ^ string_of_int (!freshCount)
      in FExists(fresh, renameFormula y var fresh)
  | FRel(name, a, xs) -> x
  | _ -> applyToSubformula renameBoundedVars x

let prenexRule (x : formula) : formula =
  match x with
  (* Negation rules *)
    FNeg(FExists(var, y)) -> FForall(var, FNeg(y))
  | FNeg(FForall(var, y)) -> FExists(var, FNeg(y))
  (* Conjunction rules *)
  | FConj(FForall (var, y), z) -> FForall(var, FConj(y, z))
  | FConj(y, FForall (var, z)) -> FForall(var, FConj(y, z))
  | FConj(FExists (var, y), z) -> FExists(var, FConj(y, z))
  | FConj(y, FExists (var, z)) -> FExists(var, FConj(y, z))
  (* Disjunction rules *)
  | FDisj(FForall (var, y), z) -> FForall(var, FDisj(y, z))
  | FDisj(y, FForall (var, z)) -> FForall(var, FDisj(y, z))
  | FDisj(FExists (var, y), z) -> FExists(var, FDisj(y, z))
  | FDisj(y, FExists (var, z)) -> FExists(var, FDisj(y, z))
  (* Implication antecedent rules *)
  | FImp(FForall(var, y), z) -> FExists(var, FImp(y, z))
  | FImp(FExists(var, y), z) -> FForall(var, FImp(y, z))
  (* Implication consequent rules *)
  | FImp(y, FForall(var, z)) -> FForall(var, FImp(y, z))
  | FImp(y, FExists(var, z)) -> FExists(var, FImp(y, z))
  | _ -> x

let rec applyPrenex (x : formula) : formula =
  if isPrenex x
  then x
  else applyPrenex (prenexRule (applyToSubformula applyPrenex x))

let compose f g x = f (g x)

let toPrenex = compose applyPrenex renameBoundedVars

let isLiteral (x : formula) : bool =
  match x with
    FRel(_, _, _) -> true
  | FNeg(FRel(_, _, _)) -> true
  | _ -> false

let rec isDisjLiterals (x : formula) : bool =
  match x with
    FDisj(y, z) -> (isDisjLiterals y) && (isDisjLiterals z)
  | _ -> isLiteral x

let rec conjunctify2 (x1 : formula) (x2 : formula) : formula =
  match x2 with
    FConj(y, z) -> FConj(conjunctify2 x1 y, conjunctify2 x1 z)
  | _ -> if isDisjLiterals x2
         then FDisj(x1, x2)
         else raise SOMETHINGWENTWRONG

let rec conjunctify1 (x1 : formula) (x2 : formula) : formula =
    if isDisjLiterals x1
    then conjunctify2 x1 x2
    else
      (match x1 with
        FConj(y, z) -> FConj(conjunctify1 y x2, conjunctify1 z x2)
      | _ -> raise SOMETHINGWENTWRONG)

let rec negCNF (x : formula) : formula =
  match x with
    FRel(_, _, _) -> FNeg(x)
  | FNeg(y) -> applyCNF y
  | FConj(y, z) -> applyCNF (FDisj(FNeg(y), FNeg(z)))
  | FDisj(y, z) -> applyCNF (FConj(FNeg(y), FNeg(z)))
  | FImp(y, z) -> applyCNF (FNeg(FDisj(FNeg(y), z)))
  | _ -> raise SOMETHINGWENTWRONG

and

applyCNF (x : formula) : formula =
  match x with
    FConj(y, z) -> FConj(applyCNF y, applyCNF z)
  | FDisj(y, z) -> conjunctify1 (applyCNF y) (applyCNF z)
  | FNeg(y) -> negCNF(y)
  | FImp(y, z) -> applyCNF (FDisj(FNeg(y), z))
  | FForall(var, y) -> FForall(var, applyCNF y)
  | FExists(var, y) -> FExists(var, applyCNF y)
  | _ -> x

let toCNF = compose applyCNF toPrenex

let e1 = FImp ((FForall ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))

let e2 = FImp ((FExists ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))
let e3 = FRel("R", 1, [TVar "x"])
let e4 = FNeg(FRel("R", 1, [TVar "x"]))
let e5 = FDisj(FConj(pSym "A", pSym "B"), FDisj(FConj(pSym "C", pSym "D"), pSym "E"))
let e6 = FDisj(FDisj(pSym "E", FConj(pSym "C", pSym "D")), FConj(pSym "A", pSym "B"))
let e7 = FDisj (FDisj (FConj (pSym "A", pSym "B"), FConj (pSym "C", pSym "D")), pSym "E")
let e8 = FNeg (FImp (FConj (FImp (pSym "A", pSym "B") , pSym "A") , pSym "B"))