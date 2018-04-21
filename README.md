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
This repository contains some [theoretical pencil-and-paper work](doc) and
[accompanying implementations](iconfluence).

## Decision Procedure
Our decision procedures require python version >= 3.6. We recommend creating a
conda environment to work in:

```bash
$ conda create --name iconfluence python=3.6
$ source activate iconfluence
```

Then, pip install the dependencies

```bash
$ pip install -r requirements.txt
```

Then, install z3 and z3py. Unfortunately, z3py is not pippable, so you'll have
to install it by hand.

```
$ cd $HOME
$ git clone https://github.com/Z3Prover/z3
$ cd z3
$ python scripts/mk_make.py --python
$ cd build
$ make
$ sudo make install
$ echo 'export PYTHONPATH="$PYTHONPATH:$HOME/z3/build/python"'
```

Then, play with the examples in [`examples/`](examples/).

```bash
$ PYTHONPATH=. python -i -m examples.all_datatypes
$ PYTHONPATH=. python -i -m examples.auction
$ PYTHONPATH=. python -i -m examples.bank_deposit_and_withdraw
$ PYTHONPATH=. python -i -m examples.bank_deposit_only
$ PYTHONPATH=. python -i -m examples.foreign_key
$ PYTHONPATH=. python -i -m examples.subsets
$ PYTHONPATH=. python -i -m examples.two_ints
```

## Runtime
Our runtime requires C++14 or newer. First, install glog, protobuf, the
protobuf compiler. On Ubuntu 14.04, this can be done as follows:

```bash
$ # Use a newer version of protobuf than is otherwise provided.
$ sudo add-apt-repository ppa:maarten-fonville/protobuf
$ sudo apt-get update
$ sudo apt-get install -y libgoogle-glog-dev libprotobuf-dev protobuf-compiler
```

Then, install libuv:

```bash
$ cd $HOME
$ git clone https://github.com/libuv/libuv
$ cd libuv
$ sh autogen.sh
$ ./configure
$ make
$ make check
$ sudo make install
```

and make sure that `/usr/local/lib` is on your `LD_LIBRARY_PATH` by adding
something like `export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib"` to
your `~/.bashrc`.

Then, `cd` into the `lucy` directory and run `make` (or `make DEBUG=0` or `make
VERBOSE=1`).
