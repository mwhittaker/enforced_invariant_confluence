type atom =
  | Var   of string
  | Const of int

type aexp =
  | Atom of atom
  | Neg  of aexp
  | Add  of aexp * aexp
  | Sub  of aexp * aexp

type bexp =
  | Eq   of aexp * aexp
  | Neq  of aexp * aexp
  | Lt   of aexp * aexp
  | Leq  of aexp * aexp
  | Gt   of aexp * aexp
  | Geq  of aexp * aexp
  | Not  of bexp
  | And  of bexp * bexp
  | Or   of bexp * bexp
  | Impl of bexp * bexp

module Abbreviations = struct
  let x  = Atom (Var "x")
  let y  = Atom (Var "y")
  let z  = Atom (Var "z")
  let var x = Atom (Var x)

  let zero  = Atom (Const 0)
  let one   = Atom (Const 1)
  let two   = Atom (Const 2)
  let three = Atom (Const 3)
  let four  = Atom (Const 4)

  let (~-) x   = Neg x
  let (+)  x y = Add (x, y)
  let (-)  x y = Sub (x, y)

  let (==) x y = Eq  (x, y)
  let (<>) x y = Neq (x, y)
  let (<)  x y = Lt  (x, y)
  let (<=) x y = Leq (x, y)
  let (>)  x y = Gt  (x, y)
  let (>=) x y = Geq (x, y)

  let (!)  a   = Not  a
  let (&&) a b = And  (a, b)
  let (||) a b = Or   (a, b)
  let (=>) a b = Impl (a, b)
end

let atom_to_string atom =
  match atom with
  | Var x   -> x
  | Const k -> string_of_int k

let rec aexp_to_string x =
  let sprintf = Printf.sprintf in
  match x with
  | Atom atom  -> atom_to_string atom
  | Neg x      -> sprintf "-(%s)" (aexp_to_string x)
  | Add (x, y) -> sprintf "(%s) + (%s)" (aexp_to_string x) (aexp_to_string y)
  | Sub (x, y) -> sprintf "(%s) - (%s)" (aexp_to_string x) (aexp_to_string y)

let rec bexp_to_string a =
  let sprintf = Printf.sprintf in
  match a with
  | Eq  (x, y)  -> sprintf "(%s) == (%s)" (aexp_to_string x) (aexp_to_string y)
  | Neq (x, y)  -> sprintf "(%s) <> (%s)" (aexp_to_string x) (aexp_to_string y)
  | Lt  (x, y)  -> sprintf "(%s) < (%s)"  (aexp_to_string x) (aexp_to_string y)
  | Leq (x, y)  -> sprintf "(%s) <= (%s)" (aexp_to_string x) (aexp_to_string y)
  | Gt  (x, y)  -> sprintf "(%s) > (%s)"  (aexp_to_string x) (aexp_to_string y)
  | Geq (x, y)  -> sprintf "(%s) >= (%s)" (aexp_to_string x) (aexp_to_string y)
  | Not  a      -> sprintf "not (%s)"     (bexp_to_string a)
  | And  (a, b) -> sprintf "(%s) && (%s)" (bexp_to_string a) (bexp_to_string b)
  | Or   (a, b) -> sprintf "(%s) || (%s)" (bexp_to_string a) (bexp_to_string b)
  | Impl (a, b) -> sprintf "(%s) => (%s)" (bexp_to_string a) (bexp_to_string b)

let atom_to_z3 atom =
  atom_to_string atom

let rec aexp_to_z3 (x: aexp) =
  let sprintf = Printf.sprintf in
  match x with
  | Atom atom  -> atom_to_string atom
  | Neg x      -> sprintf "(- %s)" (aexp_to_z3 x)
  | Add (x, y) -> sprintf "(+ %s %s)" (aexp_to_z3 x) (aexp_to_z3 y)
  | Sub (x, y) -> sprintf "(- %s %s)" (aexp_to_z3 x) (aexp_to_z3 y)

let rec bexp_to_z3 a =
  let sprintf = Printf.sprintf in
  match a with
  | Eq  (x, y)  -> sprintf "(= %s %s)" (aexp_to_string x) (aexp_to_string y)
  | Neq (x, y)  -> bexp_to_z3 (Not (Eq (x, y)))
  | Lt  (x, y)  -> sprintf "(< %s %s)"   (aexp_to_z3 x) (aexp_to_z3 y)
  | Leq (x, y)  -> sprintf "(<= %s %s)"  (aexp_to_z3 x) (aexp_to_z3 y)
  | Gt  (x, y)  -> sprintf "(> %s %s)"   (aexp_to_z3 x) (aexp_to_z3 y)
  | Geq (x, y)  -> sprintf "(>= %s %s)"  (aexp_to_z3 x) (aexp_to_z3 y)
  | Not  a      -> sprintf "(not %s)"    (bexp_to_z3 a)
  | And  (a, b) -> sprintf "(and %s %s)" (bexp_to_z3 a) (bexp_to_z3 b)
  | Or   (a, b) -> sprintf "(or %s %s)"  (bexp_to_z3 a) (bexp_to_z3 b)
  | Impl (a, b) -> sprintf "(=> %s %s)"  (bexp_to_z3 a) (bexp_to_z3 b)

let vars_of_atom (atom: atom) =
  match atom with
  | Var x -> Common.StringSet.singleton x
  | Const _ -> Common.StringSet.empty

let rec vars_of_aexp x =
  match x with
  | Atom atom  -> vars_of_atom atom
  | Neg x      -> vars_of_aexp x
  | Add (x, y)
  | Sub (x, y) -> Common.StringSet.union (vars_of_aexp x) (vars_of_aexp y)

let rec vars_of_bexp a =
  match a with
  | Eq  (x, y)
  | Neq (x, y)
  | Lt  (x, y)
  | Leq (x, y)
  | Gt  (x, y)
  | Geq (x, y)  -> Common.StringSet.union (vars_of_aexp x) (vars_of_aexp y)
  | Not  a      -> vars_of_bexp a
  | And  (a, b)
  | Or   (a, b)
  | Impl (a, b) -> Common.StringSet.union (vars_of_bexp a) (vars_of_bexp b)

(* [aexp_var_map] is like [var_map] but for arithmetic expressions. *)
let rec aexp_var_map (f: string -> aexp) (x: aexp) : aexp =
  match x with
  | Atom (Const k) as x -> x
  | Atom (Var x) -> f x
  | Neg x -> Neg (aexp_var_map f x)
  | Add (x, y) -> Add (aexp_var_map f x, aexp_var_map f y)
  | Sub (x, y) -> Sub (aexp_var_map f x, aexp_var_map f y)

let rec var_map f a =
  match a with
  | Eq  (x, y)  -> Eq   (aexp_var_map f x, aexp_var_map f y)
  | Neq (x, y)  -> Neq  (aexp_var_map f x, aexp_var_map f y)
  | Lt  (x, y)  -> Lt   (aexp_var_map f x, aexp_var_map f y)
  | Leq (x, y)  -> Leq  (aexp_var_map f x, aexp_var_map f y)
  | Gt  (x, y)  -> Gt   (aexp_var_map f x, aexp_var_map f y)
  | Geq (x, y)  -> Geq  (aexp_var_map f x, aexp_var_map f y)
  | Not  a      -> Not  (var_map f a)
  | And  (a, b) -> And  (var_map f a, var_map f b)
  | Or   (a, b) -> Or   (var_map f a, var_map f b)
  | Impl (a, b) -> Impl (var_map f a, var_map f b)
