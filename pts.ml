(*  COMP 560-2 Propositional Theorem Solver
*   Theodore (Ted) Kim
* 
*   Solver purposefully does not prematurely close tableau
*)

module PTS = 
struct

type prop =  P of string | Top | Bottom | And of prop * prop | Or of prop * prop
  | Implies of prop * prop | Not of prop

type status = Open | Closed

(* type for sequents : gamma |- delta *)
type sequent = prop list * prop list

(* type for tableau: list to be printed, list used for branching, subtableau, subtableau, status*)
type tableau = Empty 
  | Node of (bool * prop) list * (bool * prop) list * tableau * tableau * status

(* exceptions *)
exception IncorrectCase
exception SequentError

let rec disj (d : prop list) : (bool * prop) list =
  match d with
  | [d] -> [(false, d)]
  | d::ds -> (false, d)::(disj ds)
  | [] -> raise IncorrectCase

let rec conj (g : prop list) : (bool * prop) list =
  match g with
  | [g] -> [(true, g)]
  | g::gs -> (true, g)::(conj gs)
  | [] -> raise IncorrectCase

let rec isatomic (proplist : (bool * prop) list) : bool =
  match proplist with
  | [] -> true
  | [(b, P c)] -> true
  | (b, P c)::rest -> true && isatomic rest
  | (b, Bottom)::rest -> true && isatomic rest
  | (b, Top)::rest -> true && isatomic rest
  | _ -> false

let rec closable (proplist : (bool * prop) list) : bool =
  match proplist with
  | [(b, P c)] -> false
  | (true, Bottom)::rest -> true
  | (false, Top)::rest -> true
  | (b, P c)::rest -> (List.fold_left (fun h (b', P c') -> (b <> b' && c = c') || h) 
                      false rest) || closable(rest)
  | _ -> raise IncorrectCase

let rec applyalpha (proplist : (bool * prop) list) : bool * (bool * prop) * ((bool * prop) list) =
  match proplist with
  | [] -> (false, (false, P "Hi"), [])
  | (true, Not p)::rest -> (true, (true, Not p), [(false, p)])
  | (false, Not p)::rest -> (true, (false, Not p), [(true, p)])
  | (true, And (p, q))::rest -> (true, (true, And(p, q)), [(true, p); (true, q)])
  | (false, Or(p, q))::rest -> (true, (false, Or(p, q)), [(false, p); (false, q)])
  | (false, Implies(p, q))::rest -> (true, (false, Implies(p, q)), [(true, p); (false, q)])
  | _::rest -> applyalpha(rest)

let rec applybeta (proplist : (bool * prop) list) : bool * (bool * prop) * (bool * prop) *  (bool * prop) =
  match proplist with
  | [] -> (false, (false, P "Hi"), (false, P "Hi"), (false, P "Hi"))
  | (false, And(p, q))::rest -> (true, (false, And(p, q)), (false, p), (false, q))
  | (true, Or(p, q))::rest -> (true, (true, Or(p, q)), (true, p), (true, q))
  | (true, Implies(p, q))::rest -> (true, (true, Implies(p, q)), (false, p), (true, q))
  | _::rest -> applybeta(rest)

let rec remove (p : bool * prop) (proplist : (bool * prop) list) : (bool * prop) list =
  List.filter (fun x -> p <> x) proplist

let rec alphaextend (t1 : tableau) (t2 : tableau) (alphas : (bool * prop) list) : tableau * tableau =
  match t1, t2 with
  | Empty, Empty -> Node(alphas, alphas, Empty, Empty, Open), Empty
  | Node(props1, propslist1, t11, t12, Open), Empty -> let t11', t12' = alphaextend t11 t12 alphas in
      Node(props1, propslist1, t11', t12', Open), Empty
  | Node(props1, propslist1, t11, t12, Open), Node(props2, propslist2, t21, t22, Open) ->
      let t11', t12' = alphaextend t11 t12 alphas in
      let t21', t22' = alphaextend t21 t22 alphas in
      Node(props1, propslist1, t11', t12', Open), Node(props2, propslist2, t21', t22', Open)

let rec betaextend (t1 : tableau) (t2 : tableau) (beta1 : (bool * prop)) (beta2 : (bool * prop)) : tableau * tableau =
  match t1, t2 with
  | Empty, Empty -> (Node([beta1], [beta1], Empty, Empty, Open), Node([beta2], [beta2], Empty, Empty, Open))
  | Node(props1, propslist1, t11, t12, Open), Empty -> let t11', t12' = betaextend t11 t12 beta1 beta2 in
      Node(props1, propslist1, t11', t12', Open), Empty
  | Node(props1, propslist1, t11, t12, Open), Node(props2, propslist2, t21, t22, Open) ->
      let t11', t12' = betaextend t11 t12 beta1 beta2 in
      let t21', t22' = betaextend t21 t22 beta1 beta2 in
      Node(props1, propslist1, t11', t12', Open), Node(props2, propslist2, t21', t22', Open)

let rec applyrules (t : tableau) : tableau =
  match t with
  | Empty -> Empty
  | Node(_, _, _, _, Closed) -> raise IncorrectCase
  | Node(props, proplist, t1, t2, Open) -> (match proplist with
    | [] -> Node(props, proplist, applyrules t1, applyrules t2, Open)
    | p::rest -> (match applyalpha(proplist) with
        | (true, p, alphas) -> let t1', t2' = alphaextend t1 t2 alphas in
            Node(props, remove p proplist, t1', t2', Open)
        | (false, _, _) -> (match applybeta(proplist) with
            | (true, p, beta1, beta2) -> let t1', t2' = betaextend t1 t2 beta1 beta2 in
                Node(props, remove p proplist, t1', t2', Open)
            | (false, _, _, _) -> t)))

let passon (proplistnew : (bool * prop) list) (t : tableau) =
  match t with
  | Empty -> raise IncorrectCase
  | Node(props, proplist, t1, t2, Open) -> Node(props, proplist @ proplistnew, t1, t2, Open)

let rec solve' (t : tableau) : tableau =
  match t with
  | Empty -> Empty
  | Node(props, proplist, t1, t2, Open) when (proplist = []) -> Node(props, proplist, solve' t1, solve' t2, Open)
  | Node(props, proplist, Empty, Empty, Open) when isatomic(proplist) && closable(proplist) -> 
      Node(props, proplist, Empty, Empty, Closed)
  | Node(props, proplist, Empty, Empty, Open) when isatomic(proplist) -> 
      Node(props, proplist, Empty, Empty, Open)
  | Node(props, proplist, t1, Empty, Open) when isatomic(proplist) ->
      let t1' = passon proplist t1 in
        solve' (Node(props, [], t1', Empty, Open))
  | Node(props, proplist, t1, t2, Open) when isatomic(proplist) ->
      let t1' = passon proplist t1 in
      let t2' = passon proplist t2 in
        solve' (Node(props, [], t1', t2', Open))
  | t -> solve' (applyrules t)

let solve (s : sequent) : tableau =
  match s with
  | ([], []) -> raise IncorrectCase
  | ([], d) -> let delta = disj d in solve' (Node(delta, delta, Empty, Empty, Open))
  (* | (g, []) -> raise IncorrectCase *)
  | (g, d) -> let dg = conj g @ disj d in solve' (Node(dg, dg, Empty, Empty, Open))

let stringifybool (b : bool) : string =
  match b with
  | false -> "F\\ "
  | true -> "T\\ "

let rec stringifyprop' (prop : prop) : string =
  match prop with
  | P c -> c
  | Top -> "\\top"
  | Bottom -> "\\bot"
  | Not p -> "\\lnot (" ^ stringifyprop'(p) ^")"
  | Or(p, q) -> "(" ^ stringifyprop'(p) ^ "\\lor " ^ stringifyprop'(q) ^ ")"
  | And(p, q) -> "(" ^ stringifyprop'(p) ^ "\\land " ^ stringifyprop'(q) ^ ")"
  | Implies(p, q) -> "(" ^ stringifyprop'(p) ^ "\\implies " ^ stringifyprop'(q) ^ ")"

let stringifyprop ((b, prop) : bool * prop) : string =
  stringifybool b ^ " " ^ stringifyprop' prop

let rec stringifyproplist (propslist : (bool * prop) list) : string =
  match propslist with
  | [] -> ""
  | p::rest -> stringifyprop p ^ "," ^ stringifyproplist rest

let rec stringifygd' (propslist : prop list) : string =
  match propslist with
  | [] -> ""
  | p::rest -> stringifyprop' p ^ "," ^ stringifygd' rest

let stringifygd (propslist : prop list) : string =
  match propslist with
  | [] -> ""
  | _ -> let r = stringifygd' propslist in String.sub r 0 (String.length(r)-1)

let rec stringifytableau' (t : tableau) : string =
  match t with
  | Empty -> ""
  | Node(propslist, _, Empty, Empty, Closed) -> let r = stringifyproplist propslist in
      "$" ^ String.sub r 0 (String.length(r)-1) ^ "\\ \\odot$"
  | Node(propslist, _, Empty, Empty, Open) -> let r = stringifyproplist propslist in
      "$" ^ String.sub r 0 (String.length(r)-1) ^ "$"
  | Node(propslist, _, t1, Empty, status) -> let r = stringifyproplist propslist in
      "$" ^ String.sub r 0 (String.length(r)-1) ^ "$ [" ^ stringifytableau' t1 ^ "]"
  | Node(propslist, _, t1, t2, status) -> let r = stringifyproplist propslist in
      "$" ^ String.sub r 0 (String.length(r)-1) ^ "$ [" ^ stringifytableau' t1 ^ "] [" ^ stringifytableau' t2 ^ "]"

let stringifytableau (t : tableau) (sequent : string) : string =
  "\\synttree[" ^ sequent ^ "[" ^ stringifytableau' t ^ "]]"

let latexify (g, d) =
  let tableau = solve(g, d) in
  let sequent = "$F\\ " ^ stringifygd g ^ "\\vdash " ^ stringifygd d ^ "$" in 
  let header = "\\documentclass[letterpaper,12pt,oneside]{book}\n" ^
    "\\usepackage[DIV=14,BCOR=2mm,headinclude=true,footinclude=false]{typearea}\n" ^
    "\\usepackage{geometry, synttree, amsthm, amsmath, amssymb}\n"^
    "\\geometry{letterpaper, margin=1in}\n" in
  let file = "output.tex" in
  let tableau = stringifytableau tableau sequent in
  let oc = open_out file in
  let () =  Printf.fprintf oc ("%s\n\\begin{document}\n%s\n\\end{document}") header tableau in
  let () = close_out oc in
      tableau

(* tests *)
let test = ([], [Or(P "P", Not (P "P"))])
let test0 = ([And(Implies(P "P", P "Q"), P "P")], [P "Q"])
let test1 = ([And(Implies(P "P", P "Q"), Not(P "Q"))], [Not(P "P")])
let test2 = ([And(Implies(P "P", P "Q"), Implies(P "Q", P "R"))], [Implies(P "P", P "R")])
let test3 = ([And(Or(P "P", P "Q"), Not(P "P"))], [P "Q"])
let test4 = ([And(Implies(P "P", P "Q"), And(Implies(P "R", P "S"), Or(P "P", P "R")))], [Or(P "Q", P "S")])
let test5 = ([And(Implies(P "P", P "Q"), And(Implies(P "R", P "S"), Or(Not(P "P"), Not(P "S"))))], [Or(Not(P "P"), Not(P "R"))])
let test6 = ([And(Implies(P "P", P "Q"), And(Implies(P "R", P "S"), Or(P "P", Not(P "S"))))], [Or(P "Q", Not(P "R"))])
let test7 = ([And(P "P", P "Q")], [P "P"])
let test8 = ([P "P"; P "Q"], [And(P "P", P "Q")])
let test9 = ([P "P"], [Or(P "P", P "Q")])
let test10 = ([And(Implies(P "P", P "Q"), Implies(P "P", P "R"))], [Implies(P "P", And(P "P", P "Q"))])
let test11 = ([Not(And(P "P", P "Q"))], [Or(Not(P "P"), Not(P "Q"))])
let test12 = ([Not(Or(P "P", P "Q"))], [And(Not(P "P"), Not(P "Q"))])
let test13 = ([Or(P "P", P "Q")], [Or(P "Q", P "P")])
let test14 = ([And(P "P", P "Q")], [And(P "Q", P "P")])
let test15 = ([Or(P "P", Or(P "Q", P "R"))], [Or(Or(P "P", P "Q"), P "R")])
let test16 = ([And(P "P", And(P "Q", P "R"))], [And(And(P "P", P "Q"), P "R")])
let test17 = ([And(P "P", Or(P "Q", P "R"))], [Or(And(P "P", P "Q"), And(P "P", P "R"))])
let test18 = ([Or(P "P", And(P "Q", P "R"))], [And(Or(P "P", P "Q"), Or(P "P", P "R"))])
let test19 = ([P "P"], [Not(Not(P "P"))])
let test20 = ([Implies(P "P", P "Q")], [Implies(Not(P "Q"), Not(P "P"))])
let test21 = ([Implies(P "P", P "Q")], [Or(Not(P "P"), P "Q")])
let test22 = ([Implies(And(P "P", P "Q"), P "R")], [Implies(P "P", Implies(P "Q", P "R"))])
let test23 = ([Implies(P "P", Implies(P "Q", P "R"))], [Implies(And(P "P", P "Q"), P "R")])
let test24 = ([P "P"], [Or(P "P", P "P")])
let test25 = ([P "P"], [And(P "P", P "P")])
let test26 = ([], [Or(P "P", Not (P "P"))])
let test27 = ([], [Not(And(P "P", Not(P "P")))])
let opentest = ([], [And(P "P", P "P")])
let test99 = ([], [Implies(And(Or(P "C", P "A"), Or(P "C", P "B")), Or(P "C", And(P "A", P "B")))])

let s = latexify test99
end