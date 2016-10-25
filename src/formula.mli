(* Universally quantified boolean expressions. *)
type formula =
  | Bexp   of Invariant.bexp   (* a *)
  | Forall of string * formula (* forall x. a *)

module Abbreviations : sig
  val forall : string list -> Invariant.bexp -> formula
end

(* Converts a formula to a human readable string. *)
val to_string : formula -> string

(* [to_z3 f] returns a Z3 script which determines whether the negation of [f]
 * is satisfiable. That is, a script which determines whether [f] is valid. If
 * it is, a satisfying model is given. This model is a counterexample
 * witnessing the fact that the formula is not valid. *)
val to_z3_script : formula -> string
