from enum import Enum
from typing import List, Optional, Tuple

from orderedset import OrderedSet
import z3

from ..ast import EVar, Expr, Invariant
from ..checker import Checker, Decision
from ..envs import ValEnv, TypeEnv, Z3ExprEnv
from ..eval import eval_invariant
from ..typecheck import typecheck_invariant
from ..z3_ import compile
from ..z3_.fresh_name import FreshName
from ..z3_.version_env import VersionEnv
from ..z3_.z3_util import scoped

class Label(Enum):
    REACHABLE = "reachable"
    UNREACHABLE = "unreachable"

class InteractiveChecker(Checker):
    """
    An interactive invariant-confluence decision procedure.

    Recall that a state based object O is (s0, T, I)-confluent if every (s0, T,
    I)-reachable state satisfies the invariant. O is I-closed if
    invariant-satisfying states are closed under join. I-closure always implies
    (s0, T, I)-confluence, but the converse is not always true. However, if set
    of invariant-satisfying points is a subset of the set of reachable points,
    then invariant-confluence and invariant-closure are equivalent. This
    interactive decision procedure relies on the user to iteratively refine the
    invariant until it is a subset of the set of reachable points.  It then
    uses Z3 to check for invariant-closure.

    >>> from .. import *
    >>> checker = InteractiveChecker()
    >>> x = checker.int_max('x', 0)
    >>> y = checker.int_max('y', 0)
    >>> checker.add_invariant('xy_leq_0', x * y <= 0)
    >>> checker.add_transaction('x_inc', [x.assign(x + 1)])
    >>> checker.add_transaction('y_dec', [y.assign(y - 1)])
    >>> checker.check_iconfluence()
    Counterexample found.
    counterexample1 = {'x': 0, 'y': 1}.
    counterexample2 = {'x': 1, 'y': 0}.
    <Decision.UNKNOWN: 'unknown'>
    >>> checker.counterexample1_unreachable()
    >>> checker.counterexample2_reachable()
    >>> checker.refine_invariant(y <= 0)
    >>> checker.check_iconfluence()
    <Decision.YES: 'yes'>

    TODO:
        - Currently, we do not randomly explore states to label counterexamples
          as reachable. It turns out to be a bit harder than possible because
          our state explorations generates sets of values, but Z3
          counterexamples include things like Z3 function interpretations.
          We'll have to either reachable states as Z3 function interpretations
          or translate Z3 models into Python values.
        - After a user labels a counterexample as unreachable, we do not
          automatically refine the invariant to exclude this point. Again, the
          difficulty comes from the mismatch between Invariants and Z3 models.
    """
    def __init__(self, verbose: bool = False) -> None:
        Checker.__init__(self)

        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.invariant_refinements: List[Invariant] = []

        # Counterexamples.
        self.counterexample1: Optional[Z3ExprEnv] = None
        self.counterexample1_label: Optional[Label] = None
        self.counterexample2: Optional[Z3ExprEnv] = None
        self.counterexample2_label: Optional[Label] = None
        self.unreachable_counter_examples: List[Z3ExprEnv] = []
        self.reachable_counter_examples: List[Z3ExprEnv] = []

    def __str__(self):
        strings = []

        if len(self.invariant_refinements) > 0:
            strings += ['Invariant Refinements']
            for inv in self.invariant_refinements:
                strings.append(f'  {inv}')

        if (len(self.reachable_counter_examples) > 0):
            strings += ['Reachable Counter Examples']
            for c in self.reachable_counter_examples:
                strings += [f'  {c}']

        if (len(self.unreachable_counter_examples) > 0):
            strings += ['Unreachable Counter Examples']
            for c in self.unreachable_counter_examples:
                strings += [f'  {c}']

        if (self.counterexample1 is not None and
            self.counterexample2 is not None):
            strings += ['Pending Counter Examples']
            c1 = self.counterexample1
            l1 = self.counterexample1_label
            c2 = self.counterexample2
            l2 = self.counterexample2_label

            l1_str = f' [{l1}]' if l1 is not None else ''
            l2_str = f' [{l2}]' if l2 is not None else ''
            strings.append(f'  counterexample 1 == {c1}{l1_str}')
            strings.append(f'  counterexample 2 == {c2}{l2_str}')

        return '\n'.join([Checker.__str__(self)] + strings)

    def _state_satisfies_invs(self, \
                              state: ValEnv, \
                              invs: List[Invariant]) \
                              -> bool:
        return all(eval_invariant(inv, state) for inv in invs)

    def _compile_expr(self,
                      e: Expr,
                      venv: VersionEnv) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile.compile_expr(e, venv, self.type_env, self.fresh)

    def _venv_satisfies_refined_i(self, venv: VersionEnv) -> z3.ExprRef:
        zss = OrderedSet()

        for inv in self.invariants.values():
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        for inv in self.invariant_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        return z3.And(list(zss))

    def _extract_counterexample_from_model(self, \
                                           model: z3.ModelRef, \
                                           venv: VersionEnv,
                                           tenv: TypeEnv) -> Z3ExprEnv:
        z3_expr_env: Z3ExprEnv = dict()
        for (v, typ) in tenv.items():
            x = EVar(v)
            zx = compile.compile_var(x, venv, tenv)
            z3_expr_env[v] = model[zx]
        return z3_expr_env

    def _record_counterexample(self, \
                               counterexample: Z3ExprEnv, \
                               label: Label) \
                               -> None:
        if label == Label.REACHABLE:
            self.reachable_counter_examples.append(counterexample)
        else:
            assert label == Label.UNREACHABLE, label
            self.unreachable_counter_examples.append(counterexample)

    def _is_refined_i_closed(self) -> Decision:
        with scoped(self.solver):
            # Assert rhs satisfies invariant.
            lhs_venv = VersionEnv('lhs')
            self.solver.add(self._venv_satisfies_refined_i(lhs_venv))

            # Assert lhs satisfies invariant.
            rhs_venv = VersionEnv('rhs')
            self.solver.add(self._venv_satisfies_refined_i(rhs_venv))

            # Compute join.
            join_venv = VersionEnv('joined')
            zss, join_env = compile.compile_join(lhs_venv, rhs_venv, join_venv,
                                                 self.crdt_env, self.type_env,
                                                 self.fresh)
            self.solver.add(list(zss))

            # Assert join satisfies invariant.
            self.solver.add(z3.Not(self._venv_satisfies_refined_i(join_env)))

            # Display generated code.
            if self.verbose:
                print(self.solver.sexpr())

            # Check if we're I - NR closed.
            result = self.solver.check()

            # If z3 is stuck, we're stuck.
            if result == z3.unknown:
                print('Z3 got stuck!')
                return Decision.UNKNOWN

            # If there are no counterexamples, then we are invariant-closed.
            if result == z3.unsat:
                return Decision.YES

            # Otherwise, we are are not invariant-closed, and we have a
            # counterexample.
            model = self.solver.model()
            self.counterexample1 = self._extract_counterexample_from_model(
                model, lhs_venv, self.type_env)
            self.counterexample2 = self._extract_counterexample_from_model(
                model, rhs_venv, self.type_env)

            print('Counterexample found.')
            print(f'counterexample1 = {self.counterexample1}.')
            print(f'counterexample2 = {self.counterexample2}.')

            return Decision.UNKNOWN

    def check_iconfluence(self) -> Decision:
        msg = ('Counterexample {0} is unlabelled. Call ' +
               '`counterexample{0}_reachable()` to label the counterexample ' +
               'as reachable or `counterexample{0}_unreachable()` to label ' +
               'the counterexample as unreachable.')
        c1 = self.counterexample1
        l1 = self.counterexample1_label
        c2 = self.counterexample2
        l2 = self.counterexample2_label

        if (c1 is not None and l1 is None):
            print(msg.format(1))
            return Decision.UNKNOWN

        if (c2 is not None and l2 is None):
            print(msg.format(2))
            return Decision.UNKNOWN

        if (c1 is not None and c2 is not None):
            self._record_counterexample(c1, l1)
            self._record_counterexample(c2, l2)
            if (l1 == Label.REACHABLE and l2 == Label.REACHABLE):
                return Decision.NO
            else:
                self.counterexample1 = None
                self.counterexample2 = None
                self.counterexample1_label = None
                self.counterexample2_label = None

        invs = list(self.invariants.values())
        if not self._state_satisfies_invs(self.s0_vals, invs):
            return Decision.NO
        else:
            return self._is_refined_i_closed()

    def counterexample1_reachable(self):
        self.counterexample1_label = Label.REACHABLE

    def counterexample1_unreachable(self):
        self.counterexample1_label = Label.UNREACHABLE

    def counterexample2_reachable(self):
        self.counterexample2_label = Label.REACHABLE

    def counterexample2_unreachable(self):
        self.counterexample2_label = Label.UNREACHABLE

    def refine_invariant(self, inv: Invariant):
        inv = typecheck_invariant(inv, self.type_env)

        # Ensure that the start state satisfies the invariant, unless it
        # doesn't satisfy the original invariant to begin with.
        invs = list(self.invariants.values())
        if self._state_satisfies_invs(self.s0_vals, invs):
            msg = (f'The initial state {self.s0_vals} satisfies the ' +
                   f'invariant, but does not satisfy the refined invariant ' +
                   f'{inv}. This means that you\'ve incorrectly refined the ' +
                   f'invariant. Double check your refinements and try again.')
            invs = self.invariant_refinements + [inv]
            assert self._state_satisfies_invs(self.s0_vals, invs), msg

        self.invariant_refinements.append(inv)
