(*  COMP 560-2 Resolution Theorem Prover
*   Theodore (Ted) Kim
*)

module RTP = struct
open FOL
include CNF
include UNIFY

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

(* Pretty printing for clauses *)
let rec print_clause (xs : formula list) : string =
  (String.concat "" (intersperse "," (List.map show xs)))

let rec print_clauses (xs : (formula list) list) : string =
  match xs with
    [] -> ""
  | y::[] -> "{" ^ print_clause(y) ^ "}"
  | y::ys -> "{" ^ print_clause(y) ^ "}, " ^ (print_clauses ys)

let printClauses (x : (formula list) list) : unit = (print_string ("{"^(print_clauses x)^"}"); print_string "\n")

let print_bool (x : bool) : string =
  match x with
    true -> "true"
  | false -> "false"

let rec disj (d : formula list) : formula =
  match d with
    [d] -> d
  | d::ds -> FDisj(d, disj ds)
  | [] -> raise SOMETHINGWENTWRONG

let rec negdisj (d : formula list) : formula =
  match d with
    [d] -> FNeg(d)
  | d::ds -> FDisj(FNeg(d), negdisj ds)
  | [] -> raise SOMETHINGWENTWRONG

let rec conj (g : formula list) : formula =
  match g with
    [g] -> g
  | g::gs -> FConj(g, conj gs)
  | [] -> raise SOMETHINGWENTWRONG

(* Comparison test for formulas, drops predefined length of formula *)
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

(* Membershit test for formulas *)
let rec mem (x : formula list) (y : formula list) : bool =
  match x with
    [] -> true
  | x::xs -> List.mem x y && mem xs y

let rec fmem (x : formula list) (fs : (formula list) list) : bool = 
  match fs with
    [] -> false
  | g::gs -> (mem x g && List.length x = List.length g) || fmem x gs

(* Checks for formula membership of its negation and their terms *)
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

(* Checks for negated formula membership and returns the formula and its negation *)
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

(* Substitution for formulas *)
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

(* Resolves formula with list of formulas, applying substitution as necessary *)
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

(* Fresh variables to avoid capture and properly resolve *)
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

(* Checks if anything can be resolved *)
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

(* Resolves formula list against all clauses *)
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

(* Resolution either succeeds and returns true or run out of formulas in new clauses and returns false *)
let rec resolution'' (b : bool) (n : (formula list) list) (o : (formula list) list) : bool =
  if b then true else
  match n, o with
    [], o -> false
  | fl::fls, o ->
      let () = print_string "Set of new clauses: "; printClauses n in
      let () = print_string "Set of old clauses: "; printClauses o; print_string "\n" in
      let b, n', o' = resolution3 fl fls (union n o) o in
      resolution'' b n' o'

(* Start off not finished *)
let resolution' (xs : (formula list) list) : bool =
  resolution'' false xs [] 

(* Main function that skolemizes, turns formula into clauses, then applies resolution rules *)
let resolution (x : formula list) (y : formula list) : bool =
  match x, y with
    [], y -> resolution' (clausify(skolemize(FNeg(disj y))))
  | [], [] -> raise SOMETHINGWENTWRONG
  | x, [] -> resolution' (clausify(skolemize(FNeg(negdisj x))))
  | x, y -> resolution' (clausify(skolemize(conj x)) @ clausify(skolemize(FNeg(disj y))))


(* Tests *)
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

let rhsempty = resolution [FNeg(pSym "A"); pSym "A"] []

end