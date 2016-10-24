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

val atom_to_string : atom -> string
val aexp_to_string : aexp -> string
val bexp_to_string : bexp -> string

module Abbreviations: sig
  val x : aexp
  val y : aexp
  val z : aexp

  val zero  : aexp
  val one   : aexp
  val two   : aexp
  val three : aexp

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
