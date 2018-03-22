# Invariant Confluence
_Strong consistency_ allows programmers to ignore many of the complexities of a
distributed system, treating it as if it were running on a single machine.
However, enforcing strong consistency requires _coordination_, and coordination
leads to unavailability (at worst) or increased latency (at best). However,
coordination cannot always be avoided. Certain application invariants require
coordination in order to be globally enforced. Bailis et al. developed the
notion of invariant-confluence as a necessary and sufficient condition for
coordination freedom. Intuitively, a replicated object (with some start state
and set of transactions) is invariant-confluent with respect to some invariant
if the replicated object never takes on a value that violates the invariant.
Bailis characterized many common invariants (e.g. uniqueness constraints,
foreign key constraints), showing which could be maintained without
coordination. However, this characterization required hand-written proofs.
This research project aims to expand on Bailis' research with a decision
procedure to algorithmically determine when an object is invariant-confluent.

This repository contains some [theoretical pencil-and-paper work](doc), [an
early prototype](ocaml) of a decision procedure, and [a more fleshed out
prototype](iconfluence) which implements the decision procedures that have been
outlined with pencil and paper.

## Getting Started
First, install z3 and z3py. Then, pip install the dependencies in
`requirements.txt`. Then, play with the examples in [`examples/`](examples/).

```bash
$ PYTHONPATH=. python -i -m examples.all_datatypes
$ PYTHONPATH=. python -i -m examples.auction
$ PYTHONPATH=. python -i -m examples.bank_deposit_and_withdraw
$ PYTHONPATH=. python -i -m examples.bank_deposit_only
$ PYTHONPATH=. python -i -m examples.foreign_key
$ PYTHONPATH=. python -i -m examples.subsets
$ PYTHONPATH=. python -i -m examples.two_ints
```

## TODO
- Remove the `ocaml/` directory. It's a cute first implementation, but it's
  obsolete.
- If this work gets published, include a link to the paper in this README.
- Implement and mention Lucy.
