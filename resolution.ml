(*  COMP 560-2 Resolution Theorem Prover
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

type constr = term * term
type constraints = constr list

type substitution = (string * term) list

exception SOMETHINGWENTWRONG
exception CONFLICT
exception OCCURRENCE

(* -------------------------------------------------------------------------------------------------------------------- *)

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
      in let fresh = "x_" ^ string_of_int (!freshCount)
      in FForall(fresh, renameFormula y var fresh)
  | FExists(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = "x_" ^ string_of_int (!freshCount)
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

(* -------------------------------------------------------------------------------------------------------------------- *)

let showTerms (y, z : term * term) : string =
  (showTerm y) ^ " = " ^ (showTerm z)

let showC (xs : constraints) : string =
  "<" ^ (String.concat "" (intersperse "," (List.map showTerms xs))) ^ ">"

let printConstraints (x : constraints) : unit = (print_string (showC x); print_string "\n")

let rec occurs_free (x : string) (t2 : term) : bool =
  match t2 with
  | TVar y -> x = y
  | TFunction(c, 0, xs) -> false
  | TFunction (f, _, xs) ->
        List.fold_left (fun b z -> occurs_free x z ||b) false xs
  | _ -> raise SOMETHINGWENTWRONG

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

let subst2 (s : substitution) (y, z : constr) : constr =
  subst s y, subst s z

let apply_subst (s : substitution) (xs : constraints) : constraints =
  List.map (fun x -> subst2 s x) xs

let rec remove_dupes lst = 
  match lst with 
    [] -> []
  | x::xs -> x::(remove_dupes (List.filter (fun y -> y<>x) xs))

let compose_subst (g : substitution) (f : substitution) : substitution =
  let f' = List.filter (fun (x',t') -> not (List.mem_assoc x' g)) f
  in let fg = (List.map (fun (x',t') -> (x', subst f t')) g) @ f'
  in remove_dupes fg

let applyRules (y, z : constr) (xs : constraints) (s : substitution) : constraints * substitution =
  (* erasing *)
  if y = z
  then xs, s
  else
  match y, z with
    TFunction(f, fa, ftms), TFunction(g, ga, gtms) ->
      if f <> g || fa <> ga
      (* conflict *)
      then raise CONFLICT
      (* decomposition *)
      else zip ftms gtms @ xs, s
  | TVar x, z ->
      if occurs_free x z
      (* occurrence *)
      then raise OCCURRENCE
      (* elimination *)
      else let s' = (x, z)
      in apply_subst [s'] xs, compose_subst s [s']
      (* inversion *)
  | y, TVar x -> (TVar x, y)::xs, s

let rec applyUnification (x : constraints) (s : substitution) : substitution =
  match x with
    [] -> s
  | (x::xs) -> let (xs', s') = applyRules x xs s
               in applyUnification xs' s'

let rec print_subst (s : substitution) : string =
  match s with
  | [] -> ""
  | [(x,t)] -> showTerm(t)^"/"^x
  | (x,t)::xs -> showTerm(t)^"/"^x^","^(print_subst xs)

let printSubstitution (x : substitution) : unit = (print_string ("{"^(print_subst x)^"}"); print_string "\n")

let unify (x : constraints) : substitution =
  applyUnification x []

(* -------------------------------------------------------------------------------------------------------------------- *)

let rec replaceTerm (x : term) (old : string) (fresh : term) : term =
  match x with
    TVar s -> if s = old then fresh else (TVar s)
  | TFunction(name, a, xs) ->
      TFunction(name, a, List.map (fun t -> (replaceTerm t old fresh)) xs)

let rec replaceFormula (x : formula) (old : string) (fresh : term) : formula =
  match x with
  | FRel(name, a, xs) ->
      FRel(name, a, List.map (fun t -> replaceTerm t old fresh) xs)
  | _ -> applyToSubformula (fun y -> replaceFormula y old fresh) x

let rec skolemize' (x : formula) (xs : term list) : formula  =
  match x with
    FForall(var, y) -> skolemize' y (TVar(var)::xs) 
  | FExists(var, y) ->
      let () = freshCount := (!freshCount) + 1
      in let fresh = TFunction("f_" ^ string_of_int (!freshCount), List.length xs, xs)
      in skolemize' (replaceFormula y var fresh) xs
  | _ -> x

let skolemize (x : formula) : formula =
  let () = print_string "Original Formula: " ; printFormula x in
  let () = print_string "Prenex/CNF Formula: " ; printFormula (toCNF x) in
  let () = print_string "Skolemized Formula: " ; printFormula (skolemize' (toCNF x) []) in
  skolemize' (toCNF x) []

let rec clausify' (x : formula) : formula list =
  match x with
    FRel(name, a, xs) -> [FRel(name, a, xs)]
  | FNeg(FRel(name, a, xs)) -> [FNeg(FRel(name, a, xs))]
  | FDisj(y, z) -> clausify' y @ clausify' z
  | FTruth -> [FTruth]
  | FFalsity -> [FFalsity]
  | _ -> raise SOMETHINGWENTWRONG

let rec clausify (x : formula) : (formula list) list =
  match x with
    FRel(name, a, xs) -> [[FRel(name, a, xs)]]
  | FNeg(FRel(name, a, xs)) -> [[FNeg(FRel(name, a, xs))]]
  | FTruth -> [[FTruth]]
  | FFalsity -> [[FFalsity]]
  | FDisj(y, z) -> [clausify' y @ clausify' z]
  | FConj(y, z) -> clausify y @ clausify z
  | _ -> raise SOMETHINGWENTWRONG

let rec print_clause (xs : formula list) : string =
  (String.concat "" (intersperse "," (List.map show xs)))

let rec print_clauses (xs : (formula list) list) : string =
  match xs with
    [] -> ""
  | y::[] -> "{" ^ print_clause(y) ^ "}"
  | y::ys -> "{" ^ print_clause(y) ^ "}, " ^ (print_clauses ys)

let printClauses (x : (formula list) list) : unit = (print_string ("{"^(print_clauses x)^"}"); print_string "\n")

let rec disj (d : formula list) : formula =
  match d with
    [d] -> d
  | d::ds -> FDisj(d, disj ds)
  | [] -> raise SOMETHINGWENTWRONG

let rec conj (g : formula list) : formula =
  match g with
    [g] -> g
  | g::gs -> FConj(g, conj gs)
  | [] -> raise SOMETHINGWENTWRONG

let same_formula (f : formula) (g : formula) : bool =
  match f, g with
    FRel(name1, a1, xs1), FRel(name2, a2, xs2) -> name1 = name2 && xs1 = xs2
  | FNeg(FRel(name1, a1, xs1)), FNeg(FRel(name2, a2, xs2)) -> name1 = name2 && xs1 = xs2
  | _ -> false

let rec same_formulas (f : formula list) (g: formula list) : bool =
  match f, g with
    [], [] -> true
  | [], g -> false
  | f, [] -> false
  | f'::fs', g -> if List.fold_right (fun g' b -> same_formula f' g' || b) g false
               then same_formulas fs' (List.filter(fun g' -> same_formula f' g') g)
               else false

let rec union (n : (formula list) list) (o : (formula list) list) : (formula list) list =
  match n with
    [] -> List.rev o
  | fl::fls -> union fls (fl::List.filter (fun f -> not(same_formulas f fl)) o)

let rec union' (n : formula list) (o : formula list) : formula list =
  match n with
    [] -> List.rev o
  | fl::fls -> union' fls (fl::List.filter (fun f -> not(same_formula f fl)) o)

let rec mem (x : formula list) (y : formula list) : bool =
  match x with
    [] -> true
  | x::xs -> List.mem x y && mem xs y

let rec fmem (x : formula list) (fs : (formula list) list) : bool = 
  match fs with
    [] -> false
  | g::gs -> (mem x g && List.length x = List.length g) || fmem x gs

let rec negmem (f : formula) (n : formula list) : bool * term list * term list =
  match n with
    [] -> false, [], []
  | FRel(name1, a1, xs1)::ns -> (match f with
                                   FNeg(FRel(name2, a2, xs2)) -> if name1 = name2 then true, xs1, xs2
                                                                 else negmem f ns
                                 | _ -> negmem f ns)
  | FNeg(FRel(name1, a1, xs1))::ns -> (match f with
                                         FRel(name2, a2, xs2) -> if name1 = name2 then true, xs1, xs2
                                                                 else negmem f ns
                                       | _ -> negmem f ns)
  | _ -> raise SOMETHINGWENTWRONG

let rec negmem' (f : formula) (n : formula list) : formula * formula =
  match n with
    [] -> raise SOMETHINGWENTWRONG
  | FRel(name1, a1, xs1)::ns -> (match f with
                                   FNeg(FRel(name2, a2, xs2)) -> if name1 = name2 then
                                                                 FNeg(FRel(name2, a2, xs2)), FRel(name1, a1, xs1)
                                                                 else negmem' f ns
                                 | _ -> negmem' f ns)
  | FNeg(FRel(name1, a1, xs1))::ns -> (match f with
                                         FRel(name2, a2, xs2) -> if name1 = name2 then
                                                                 FRel(name2, a2, xs2), FNeg(FRel(name1, a1, xs1))
                                                                 else negmem' f ns
                                       | _ -> negmem' f ns)
  | _ -> raise SOMETHINGWENTWRONG

let rec substf (s : substitution) (f : formula) : formula =
  match f with
    FRel(name, a, xs) -> FRel(name, a, List.map (fun x -> subst s x)  xs)
  | FConj(y, z) -> FConj(substf s y, substf s z)
  | FDisj(y, z) -> FDisj(substf s y, substf s z)
  | FImp(y, z) -> FImp(substf s y, substf s z)
  | FNeg(y) -> FNeg(substf s y)
  | FTruth -> FTruth
  | FFalsity -> FFalsity
  | _ -> raise SOMETHINGWENTWRONG

let apply_substf (s : substitution) (xs : formula list) : formula list =
  List.map (fun x -> substf s x) xs

let rec resolve (f : formula) (fl : formula list) (g : formula list) (theta : substitution) : formula list = 
  let f1, f2 = negmem' f g in
(*   let () = print_string "f1: "; printFormula f1 in
  let () = print_string "f2: "; printFormula f2 in
  let () = print_string "fl: "; print_string (print_clause fl); print_string "\n" in
  let () = print_string "g: "; print_string (print_clause g); print_string "\n" in *)
  let f1' = List.filter (fun h -> not(same_formula (substf theta f1) h)) (apply_substf theta fl) in
  let f2' = List.filter (fun h -> not(same_formula (substf theta f2) h)) (apply_substf theta g) in
(*   let () = print_string "f1': "; print_string (print_clause f1'); print_string "\n" in
  let () = print_string "f2': "; print_string (print_clause f2'); print_string "\n" in
  let () = print_string "f1' U f2' : "; print_string (print_clause (union' f1' f2')); print_string "\n" in *)
  union' f1' f2'

let rec collectVars (t : term list) (sl : string list) : string list =
  match t with
    [] -> sl
  | TVar s::ts -> collectVars ts (s::sl)
  | TFunction(name, a, xs)::ts -> collectVars ts (collectVars xs (name::sl))

let rec makeFreshVars' (sl : string list) : substitution =
  match sl with
    [] -> []
  | s::ss -> let () = freshCount := (!freshCount) + 1 in
             let fresh = "x_" ^ string_of_int (!freshCount) in
             (s, TVar fresh)::(makeFreshVars' ss)

let makeFreshVars (t : term list) : substitution =
  let vars = collectVars t [] in
  makeFreshVars' vars

let rec resolvable (fl : formula list) (g : formula list) : bool * substitution * formula =
  match fl with
    [] -> false, [], FRel("what", 0, [])
  | f::fs -> let b, xs1, xs2 = negmem f g in
             if b then
              try
               let xs1subst = makeFreshVars xs1 in
(*                let () = printSubstitution xs1subst in *)
               let xs1' = List.map (fun x -> subst xs1subst x) xs1 in
               let xs2subst = makeFreshVars xs2 in
               let xs2' = List.map (fun x -> subst xs2subst x) xs2 in
               let cons = zip xs1' xs2' in
               let subst = unify cons in
               true, subst, f
              with
              | _ -> false, [], FRel("what", 0, [])
             else resolvable fs g

let print_bool (x : bool) : string =
  match x with
    true -> "true"
  | false -> "false"

let rec resolution3 (fl : formula list) (fls : (formula list) list) (no : (formula list) list) (o : (formula list) list) : bool * (formula list) list * (formula list) list  =
  match no with
    [] -> false, fls, o
  | g::gs -> 
(*       let () = print_string "fl: "; print_string (print_clause fl); print_string "\n" in
      let () = print_string "fls: "; printClauses fls in   
      let () = print_string "no: "; printClauses no in
      let () = print_string "o: "; printClauses o in *)
      let b, subst, f = resolvable fl g in
      (* let () = print_string "subst: "; printSubstitution subst;  print_string "\n" in *)
             if b
             then let k = resolve f fl g subst in
(*              let () = print_string "k: "; print_string (print_clause k); print_string "\n" in
             let () = print_string "mem k: "; print_string (print_bool (fmem k (union (fl::fls) o))); print_string "\n" in *)
                  if List.length k = 0 then true, fls, fl::o
                  else
                  if not (fmem k (union (fl::fls) o))
                  then false, k::fls, fl::o
                  else resolution3 fl fls gs (fl::o)
             else resolution3 fl fls gs o

let rec resolution'' (b : bool) (n : (formula list) list) (o : (formula list) list) : bool =
  if b then true else
  match n, o with
    [], o -> false
  | fl::fls, o ->
      let () = print_string "Set of new clauses: "; printClauses n in
      let () = print_string "Set of old clauses: "; printClauses o; print_string "\n" in
      let b, n', o' = resolution3 fl fls (union n o) o in
      resolution'' b n' o'

let resolution' (xs : (formula list) list) : bool =
  resolution'' false xs [] 

let resolution (x : formula list) (y : formula list) : bool =
  match x, y with
    [], y -> resolution' (clausify(skolemize(FNeg(disj y))))
  | [], [] -> raise SOMETHINGWENTWRONG
  | x, y -> resolution' (clausify(skolemize(conj x)) @ clausify(skolemize(FNeg(disj y))))

let e1 = FImp ((FForall ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))

let e2 = FImp ((FExists ("x", (FRel ("R", 1, [TVar "x"])))),
               (FExists ("x", (FRel ("R", 1, [TVar "x"])))))

let e3 = resolution [FExists("x", FDisj(FRel("P", 1, [TVar "x"]), FRel("Q", 1, [TVar "x"])))]
                    [FDisj(FExists ("x", FRel("P", 1, [TVar "x"])),(FExists ("x", FRel("Q", 1, [TVar "x"]))))] 

let e4 = resolution []
                    [FExists("y", FImp(FRel("D", 1, [TVar "y"]), FForall("x", FRel("D", 1, [TVar "x"]))))] 

let e5 = resolution []
                    [FImp(FForall("x", FRel("P", 1, [TVar "x"])), FExists("x", FRel("P", 1, [TVar "x"])))]

let e12 = resolution []
          [FImp (FExists ("x", FDisj (FRel ("P", 1, [TVar "x"]), FRel ("Q", 1 , [TVar "x"]))) ,
                FDisj (FExists ("x" , FRel ("P", 1, [TVar "x"])) , FExists("x" , FRel ("Q" , 1, [TVar "x"]))))]

let e13 = resolution []
          [FImp (FConj (FForall ("x", FNeg(FRel ("P" , 1, [TVar "x"]) )) ,
                       FForall ("x", FImp (FRel ("Q",1,[TVar "x"]) , FRel ("P",1,[TVar "x"]))))
                       , FForall ("x", FNeg (FRel ("Q", 1, [TVar "x"]))))]

let s1e18 = resolution []
            [FImp (FConj (FRel ("P", 1, [(TFunction ("0", 0, []))]) , FForall ("x" , FImp (FRel ("P" , 1 , [TVar "x"]) , FRel ("Q" , 1 , [TVar "x"])))) , FRel ("Q", 1 , [TFunction ("0",0,[])]))]


let e10 = resolution []
          [FImp (FDisj(FConj(pSym "A", pSym "B"), FDisj(FConj(pSym "C", pSym "D"), pSym "E")) , FDisj(FDisj(pSym "E", FConj(pSym "C", pSym "D")), FConj(pSym "A", pSym "B")))]



 let s3e17 = resolution []
            [FImp (FImp (FExists ("x" , FRel ("P", 1, [TVar "x"])) , FForall ("x" , FRel ("Q", 1, [TVar "x"])) ) ,
                  FForall ("x" , FImp (FRel ("P", 1, [TVar "x"]) , FRel ("Q", 1, [TVar "x"]) )))]

let fail = resolution []
           [FImp(FExists( "x", FRel ("P", 1, [TVar "x"])), FForall("x", FRel ("P", 1, [TVar "x"])))]