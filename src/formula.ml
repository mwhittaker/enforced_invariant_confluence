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

let rec to_z3 (f: formula) =
  match f with
  | Bexp a -> Invariant.bexp_to_z3 a
  | Forall (x, a) -> Printf.sprintf "(forall ((%s Int)) %s)" x (to_z3 a)

let to_z3_validity_check f =
  let lines = [
    Printf.sprintf "(define-fun conjecture () Bool %s)" (to_z3 f);
    "(assert (not conjecture))";
    "(check-sat)"
  ] in
  String.concat "\n" lines
