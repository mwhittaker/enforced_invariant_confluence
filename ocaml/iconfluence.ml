type txn = int Common.StringMap.t

(* [d x n] returns the string dxn. *)
let d (x: string) (n: int) : string =
  Printf.sprintf "d%s%d" x n

(* [and_all bs] returns a formula equivalent to the conjunction of [as]. *)
let and_all (bs: Invariant.bexp list) : Invariant.bexp =
  match bs with
  | [] -> Invariant.Abbreviations.(one == one)
  | b::bs -> List.fold_left (fun acc b -> Invariant.And (acc, b)) b bs

(* [or_all bs] returns a formula equivalent to the disjunction of [as]. *)
let or_all (bs: Invariant.bexp list) : Invariant.bexp =
  match bs with
  | [] -> Invariant.Abbreviations.(one == two)
  | b::bs -> List.fold_left (fun acc b -> Invariant.Or (acc, b)) b bs

(* [txn_to_formula vars n txn] returns a formula encoding of [txn] assuming the
 * invariant references only variables in [vars]. Variable "x" is converted to
 * "dxn". Examples:
 *   - txn_to_formula {"x"} 1 {"x": 1} ==> dx1 == 1
 *   - txn_to_formula {"x"} 1 {"x": 1, "y": 2} ==> dx1 == 1
 *   - txn_to_formula {"x", "y"} 1 {"x": 1, "y": 2} ==> dx1 == 1 && dy1 == 2
 *)
let txn_to_formula (vars: Common.StringSet.t) (n: int) (txn: txn) : Invariant.bexp =
  let module I = Invariant in
  Common.StringMap.bindings txn
  |> List.filter (fun (x, _) -> Common.StringSet.mem x vars)
  |> List.map (fun (x, k) -> I.(Eq ((Atom (Var (d x n))), (Atom (Const k)))))
  |> and_all

let iconfluent_formula txns i =
  let module I = Invariant in
  let module IA = I.Abbreviations in

  let vars = I.vars_of_bexp i in
  let vars_list = Common.StringSet.elements vars in
  let dvars1 = List.map (fun x -> d x 1) vars_list in
  let dvars2 = List.map (fun x -> d x 2) vars_list in

  let txns1 = or_all (List.map (txn_to_formula vars 1) txns) in
  let txns2 = or_all (List.map (txn_to_formula vars 2) txns) in
  let di1 = I.var_map (fun w -> IA.(var w + var (d w 1))) i in
  let di2 = I.var_map (fun w -> IA.(var w + var (d w 2))) i in
  let di12 = I.var_map (fun w -> IA.(var w + var (d w 1) + var (d w 2))) i in
  let formula = IA.((txns1 && txns2) => (i => (di1 => (di2 => di12)))) in

  Formula.Abbreviations.forall (vars_list @ dvars1 @ dvars2) formula
