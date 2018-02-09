This directory contains an early prototype of an invariant-confluence decision
procedure implemented in OCaml. It only supports integers with blind
increment/decrement transactions.

```bash
$ make
$ z3 <(./example.byte)
unsat # a.k.a. invariant confluent
```
