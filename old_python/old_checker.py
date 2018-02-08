from typing import Dict, List, Optional, Set, Tuple

from z3 import And, Solver, Not, BoolRef

from . import max_int
from .ast import Assign, Expr, Predicate
from .env import Env
from .types import Type
from .z3util import scoped

Transaction = List[Assign]

class Checker:
    def __init__(self):
        self.vs: Dict[str, Type] = dict()
        self.transactions: Dict[str, Transaction] = dict()
        self.invariants: List[Predicate] = []

        self.txn_counter = 0
        self.max_int_counter = 0

    def check(self):
        solver = Solver()
        self._check_transactions_commute(solver)
        self._check_join_is_apply(solver)
        self._check_one_di_confluence(solver)

    def max_int(self, name: str = None) -> max_int.Var:
        name = name or self._get_fresh_max_int_name()
        assert name not in self.vs
        self.vs[name] = Type.MAX_INT
        return max_int.Var(name)

    def add_transaction(self, name: Optional[str], txn: List[Assign]) -> None:
        name = name or self._get_fresh_txn_name()
        assert name not in self.transactions, (name, self.transactions)
        self.transactions[name] = txn

    def add_invariant(self, invariant: Predicate) -> None:
        self.invariants.append(invariant)

    def _get_fresh_txn_name(self) -> str:
        name = f'txn_{self.txn_counter}'
        self.txn_counter += 1
        return name

    def _get_fresh_max_int_name(self) -> str:
        name = f'txn_{self.max_int_counter}'
        self.max_int_counter += 1
        return name

    def _txn_to_z3(self, txn: Transaction, env: Env) -> \
                   Tuple[List[BoolRef], Env]:
        bexprs: List[BoolRef] = []
        for assign in txn:
            bexpr, env = assign.to_z3(env)
            bexprs.append(bexpr)
        return (bexprs, env)

    def _run_txn(self, txn: Transaction, env: Env, solver: Solver) -> Env:
        bexprs, env = self._txn_to_z3(txn, env)
        for bexpr in bexprs:
            solver.add(bexpr)
        return env

    def _envs_equal_to_z3(self, env1: Env, env2: Env) -> BoolRef:
        eqs = [env1.get_z3_var(v) == env2.get_z3_var(v)
               for v in self.vs
               if env1.get_name(v) != env2.get_name(v)]
        return And(*eqs)

    def _check_transactions_commute(self, solver: Solver) -> None:
        for (t_name, t) in self.transactions.items():
            for (u_name, u) in self.transactions.items():
                if t_name <= u_name:
                    continue

                with scoped(solver):
                    original_env = Env(self.vs)
                    u_env = original_env.with_suffix(f'{u_name}')
                    u_env = self._run_txn(u, u_env, solver)
                    t_env = original_env.with_suffix(f'{t_name}')
                    t_env = self._run_txn(t, t_env, solver)
                    tu_env = u_env.with_suffix(f'{t_name}_{u_name}')
                    tu_env = self._run_txn(t, tu_env, solver)
                    ut_env = t_env.with_suffix(f'{u_name}_{t_name}')
                    ut_env = self._run_txn(u, ut_env, solver)
                    solver.add(Not(self._envs_equal_to_z3(tu_env, ut_env)))
                    print(solver.sexpr())
                    print(solver.check())

    def _check_join_is_apply(self, solver: Solver) -> None:
        for (t_name, t) in self.transactions.items():
            for (u_name, u) in self.transactions.items():
                if t_name <= u_name:
                    continue

                with scoped(solver):
                    original_env = Env(self.vs)
                    u_env = original_env.with_suffix(f'{u_name}')
                    u_env = self._run_txn(u, u_env, solver)
                    t_env = original_env.with_suffix(f'{t_name}')
                    t_env = self._run_txn(t, t_env, solver)


                    tu_env = u_env.with_suffix(f'{t_name}_{u_name}')
                    tu_env = self._run_txn(t, tu_env, solver)

                    tu_env = u_env.with_suffix(f'{t_name}_join_{u_name}')
                    tu_env = self._run_txn(t, tu_env, solver)

                    ut_env = t_env.with_suffix(f'{u_name}_{t_name}')
                    ut_env = self._run_txn(u, ut_env, solver)

                    solver.add(Not(self._envs_equal_to_z3(tu_env, ut_env)))
                    print(solver.sexpr())
                    print(solver.check())

    def _check_one_di_confluence(self, solver: Solver) -> None:
        pass

def main() -> None:
    checker = Checker()
    x = checker.max_int('x')
    y = checker.max_int('y')
    checker.add_transaction('incr', [
        max_int.Assign(x, max_int.Add(x, max_int.Const(1))),
        max_int.Assign(y, max_int.Add(y, max_int.Const(1))),
    ])
    checker.add_transaction('swap', [
        max_int.Assign(x, y),
        max_int.Assign(y, x),
    ])
    checker.add_invariant(max_int.Eq(x, y))
    checker.check()

if __name__ == '__main__':
    main()
