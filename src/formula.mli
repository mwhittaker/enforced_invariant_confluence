(* Universally quantified boolean expressions. *)
type formula =
  | Bexp   of Invariant.bexp   (* 1 = 2 *)
  | Forall of string * formula (* forall x. forall y. x = y => y = x *)

module Abbreviations : sig
  val forall : string list -> Invariant.bexp -> formula
end

(* Converts a formula to a human readable string. *)
val to_string : formula -> string

(* Converts a formula to a Z3 sexp. *)
val to_z3 : formula -> string

(* [to_z3_validity_check f] returns a Z3 script which determines whether the
 * negation of [f] is satisfiable. *)
val to_z3_validity_check : formula -> string
