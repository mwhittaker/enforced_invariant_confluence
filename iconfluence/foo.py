(* x = IntMax() *)
(*  *)
(* x = BoolOr() *)
(*  *)
(* y = TwoPSet() *)
(*  *)
(* x = Tuple0() *)
(*  *)
(* x = Tuple1(Int()) *)
(*  *)
(* x = Tuple2(Int(), Tuple2(Int(), Bool())) *)
(*  *)
(* x = Set(Bool()) *)
(*  *)
(* y = Map(Bool(), Tuple(Int())) *)
(*  *)
(*  *)

type raw_type =
  | Int
  | Bool
  | Tuple2 of (raw_type * raw_type)
  | Set of raw_type

type user_type =
  | IntMax
  | IntMin
  | BoolOr
  | BoolAnd
  | Tuple2 of (user_type * user_type)
  | SetUnion of (user_type)

type statement =
  | Assign of var * expr

type expr =
  | Int of int
  | Bool of bool
  | Tuple2 of expr * expr
  | ...

type int_expr =
  | Const of int
  | IntVar of string
  | BoolVar of string
  | TwoPVar of string
  | ...
  | Sum of (int_expr * int_expr)
  | Diff of (int_expr * int_expr)
  | ...

x = IntMax('x')
y = IntMin('y')
