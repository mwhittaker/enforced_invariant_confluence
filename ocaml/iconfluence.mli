(* Transactions are modelled as maps from variables to integers. For example,
 * the transaction {"x": 1, "y": -2} represents a transaction that increments
 * "x" by 1 and decrements "y" as -2. *)
type txn = int Common.StringMap.t

(* [iconfluent_formula T I] returns whether a formula which is a tautology if
 * and only if T is I-confluent with respect to I. See README.pdf for
 * information on how this formula is constructed. *)
val iconfluent_formula : txn list -> Invariant.bexp -> Formula.formula
