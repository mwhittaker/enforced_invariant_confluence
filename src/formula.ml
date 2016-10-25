type formula =
  | Bexp   of Invariant.bexp
  | Forall of string * formula

module Abbreviations = struct
  let forall xs f =
    List.fold_right (fun x f -> Forall (x, f)) xs (Bexp f)
end

let rec to_string f =
  match f with
  | Bexp a -> Invariant.bexp_to_string a
  | Forall (x, a) -> Printf.sprintf "forall %s. (%s)" x (to_string a)

let to_z3_script f =
  (* [strip_quantifiers f] returns a pair of the quantifiers in [f] and the
   * boolean expression in [f]. For example, `forall x. forall y. forall z. a`
   * would be converted to `(["x"; "y"; "z"], a)`. *)
  let rec strip_quantifiers (f: formula) : string list * Invariant.bexp =
    match f with
    | Bexp a -> ([], a)
    | Forall (x, f) ->
        let (xs, a) = strip_quantifiers f in
        (x::xs, a)
  in

  let (xs, a) = strip_quantifiers f in
  let declare_xs = List.map (Printf.sprintf "(declare-const %s Int)") xs in
  let check_conjecture = [
    Printf.sprintf "(define-fun conjecture () Bool %s)" (Invariant.bexp_to_z3 a);
    "(assert (not conjecture))";
    "(check-sat)";
    "(get-model)";
  ] in
  String.concat "\n" (declare_xs @ check_conjecture)
