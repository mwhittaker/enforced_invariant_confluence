# Enforced Invariant Confluence
*Strong consistency* allows programmers to ignore many of the complexities of a
distributed system, treating it as if it were running on a single machine.
However, enforcing strong consistency requires *coordination*, and coordination
leads to unavailability (at worst) or increased latency (at best). However,
coordination cannot always be avoided.  Certain application invariants require
coordination in order to be globally enforced. Bailis et al. developed the
notion of invariant confluence (I-confluence) as a necessary and sufficient
condition for coordination freedom. Intuitively, a set of transactions is
I-confluent with respect to some invariant `I` if merging database states that
satisfy `I` always results in a database state that also satisfies `I`.  Bailis
characterized many common invariants (e.g. uniqueness constraints, foreign key
constraints), showing which could be maintained without coordination. However,
this characterization required hand-written proofs. This research project aims
to expand on Bailis' research by providing a set of CRDTs, a language of
invariants, and a language of transactions that facilitates the ability for
I-confluence to be determined algorithmically. An I-confluence decision
procedure would allow programmers to guarantee that their programs can execute
without coordination.

This repository contains some [theoretical pencil-and-paper work](doc) to
characterize with which CRDTs and invariant languages can I-confluence be
enforced. It also contains some [an early prototype](ocaml) and [a more fleshed
out prototype](iconfluence) which implement the decision procedures that have
been outlined with pencil-and-paper.
