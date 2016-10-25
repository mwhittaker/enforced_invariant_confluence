(* [txn_of_list bindings] constructs a transaction from an association list. *)
let txn_of_list (bindings: (string * int) list) : Iconfluence.txn =
  let module SM = Common.StringMap in
  List.fold_left (fun txn (x, k) -> SM.add x k txn) SM.empty bindings

let main () : unit =
  (* These transactions are invariant confluent with respect to inv. *)
  let txns = [
    txn_of_list [("x", 0); ("y", 1)];
    txn_of_list [("x", 0); ("y", 2)];
    txn_of_list [("x", 1); ("y", 2)];
    txn_of_list [("x", 2); ("y", 2)];
    txn_of_list [("x", 9); ("y", 0)];
  ] in

  (* See README.pdf *)
  let module IA = Invariant.Abbreviations in
  let inva = IA.(x + y >= zero) in
  let invb = IA.(x - y <= zero) in
  let invc = IA.(y >= zero) in
  let invd = IA.(y >= four) in
  let inv = IA.((inva && invb && invc) || invd) in

  Iconfluence.iconfluent_formula txns inv
  |> Formula.to_z3_validity_check
  |> print_endline

let () = main ()
