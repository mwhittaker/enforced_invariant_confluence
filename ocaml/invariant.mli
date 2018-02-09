(**
 * An invariant language formed from the unquantified conjunction, disjunction,
 * and negation of linear equations and inequalities over integer constants and
 * integer-valued variables.
 *)

(** Atoms *)
type atom =
  | Var   of string (* x, y, z *)
  | Const of int    (* ..., -1, 0, 1, ... *)

(** Arithmetic expressions. *)
type aexp =
  | Atom of atom
  | Neg  of aexp        (* - *)
  | Add  of aexp * aexp (* + *)
  | Sub  of aexp * aexp (* - *)

(** Boolean expressions. *)
type bexp =
  | Eq   of aexp * aexp (* =  *)
  | Neq  of aexp * aexp (* <> *)
  | Lt   of aexp * aexp (* <  *)
  | Leq  of aexp * aexp (* <= *)
  | Gt   of aexp * aexp (* >  *)
  | Geq  of aexp * aexp (* >= *)
  | Not  of bexp        (* not *)
  | And  of bexp * bexp (* and *)
  | Or   of bexp * bexp (* or  *)
  | Impl of bexp * bexp (* implication *)

module Abbreviations : sig
  val x : aexp
  val y : aexp
  val z : aexp
  val var : string -> aexp

  val zero  : aexp
  val one   : aexp
  val two   : aexp
  val three : aexp
  val four  : aexp

  val (~-) : aexp -> aexp
  val (+)  : aexp -> aexp -> aexp
  val (-)  : aexp -> aexp -> aexp

  val (==) : aexp -> aexp -> bexp
  val (<>) : aexp -> aexp -> bexp
  val (<)  : aexp -> aexp -> bexp
  val (<=) : aexp -> aexp -> bexp
  val (>)  : aexp -> aexp -> bexp
  val (>=) : aexp -> aexp -> bexp

  val (!)  : bexp -> bexp
  val (&&) : bexp -> bexp -> bexp
  val (||) : bexp -> bexp -> bexp
  val (=>) : bexp -> bexp -> bexp
end

(* Converts an atom, aexp, or bexp to a human readable string. *)
val atom_to_string : atom -> string
val aexp_to_string : aexp -> string
val bexp_to_string : bexp -> string

(* Converts an atom, aexp, or bexp to a Z3 sexp. *)
val atom_to_z3 : atom -> string
val aexp_to_z3 : aexp -> string
val bexp_to_z3 : bexp -> string

(* Returns the set of variables appearing in an atom, aexp, or bexp. *)
val vars_of_atom : atom -> Common.StringSet.t
val vars_of_aexp : aexp -> Common.StringSet.t
val vars_of_bexp : bexp -> Common.StringSet.t

(* [var_map f a] returns a boolean expression [a'] where all variables [x] in
 * [a] have been replaced with [f x]. *)
val var_map : (string -> aexp) -> bexp -> bexp
