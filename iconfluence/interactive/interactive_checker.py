from enum import Enum
from textwrap import wrap
from typing import List, Optional, Tuple

from colored import attr, fg
from orderedset import OrderedSet
import z3

from ..ast import (EVar, EBool, EBoolAnd, EBoolNot, Expr, Invariant,
                   typed_coerce)
from ..checker import Checker, Decision
from ..envs import ExprEnv, ValEnv, TypeEnv, Z3ExprEnv
from ..eval import eval_invariant
from ..state_explorer import StateExplorer
from ..typecheck import typecheck_expr, typecheck_invariant
from ..z3_ import compile
from ..z3_.fresh_name import FreshName
from ..z3_.model import InfiniteMap, InfiniteSet, model_to_state
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
    >>> checker.check()
    The following two states (i.e. lhs and rhs) satisfy the (refined) invariant, but
    their join does not. Please use the lhs_reachable(), lhs_unreachable(),
    rhs_reachable(), and rhs_unreachable() methods to label the states as reachable
    or unreachable.
    <BLANKLINE>
      lhs = {'x': 0, 'y': 1}.
      rhs [Label.REACHABLE] = {'x': 1, 'y': 0}.
      lhs join rhs = {'x': 1, 'y': 1}.
    <Decision.UNKNOWN: 'unknown'>
    >>> checker.lhs_unreachable()
    >>> checker.rhs_reachable()
    >>> checker.refine_invariant(y <= 0)
    >>> checker.check()
    <Decision.YES: 'yes'>
    """
    def __init__(self,
                 num_explored_states_per_step: int = 100,
                 verbose: bool = False) \
                 -> None:
        Checker.__init__(self)

        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.invariant_refinements: List[Invariant] = []

        # State explorer.
        self.num_explored_states_per_step = num_explored_states_per_step
        self.state_explorer = StateExplorer(self.crdt_env, self.s0_vals,
                                            self.invariants, self.transactions)

        # Counterexamples.
        self.lhs: Optional[ValEnv] = None
        self.lhs_label: Optional[Label] = None
        self.rhs: Optional[ValEnv] = None
        self.rhs_label: Optional[Label] = None
        self.unreachable: List[ValEnv] = []

    def __str__(self):
        strings = []

        if len(self.invariant_refinements) > 0:
            strings += ['Invariant Refinements']
            for inv in self.invariant_refinements:
                strings.append(f'  {inv}')

        strings += ['Reachable States']
        strings += [f'  ...']
        for s in self.state_explorer.states[-10:]:
            strings += [f'  {s}']

        if (len(self.unreachable) > 0):
            strings += ['Unreachable States']
            for s in self.unreachable:
                strings += [f'  {s}']

        if (self.lhs is not None and
            self.rhs is not None):
            strings += ['Pending States']
            self.lhs = self.lhs
            self.lhs_label = self.lhs_label
            self.rhs = self.rhs
            self.rhs_label = self.rhs_label

            lstr = f' [{self.lhs_label}]' if self.lhs_label is not None else ''
            rstr = f' [{self.rhs_label}]' if self.rhs_label is not None else ''
            strings.append(f'  lhs == {self.lhs}{lstr}')
            strings.append(f'  rhs == {self.rhs}{rstr}')

        return '\n'.join([Checker.__str__(self)] + strings)

    def _wrap_print(self, s: str) -> None:
        print('\n'.join(wrap(s, 80)))

    def _compile_expr(self,
                      e: Expr,
                      venv: VersionEnv) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile.compile_expr(e, venv, self.type_env, self.fresh)

    def _state_satisfies_invs(self, \
                              state: ValEnv, \
                              invs: List[Invariant]) \
                              -> bool:
        return all(eval_invariant(inv, state) for inv in invs)

    def _venv_satisfies_refined_i(self, venv: VersionEnv) -> OrderedSet:
        zss = OrderedSet()

        for inv in list(self.invariants.values()) + self.invariant_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        return zss

    def _venv_doesnt_satisfy_refined_i(self, venv: VersionEnv) -> OrderedSet:
        zss = OrderedSet()
        zes = OrderedSet()

        for inv in list(self.invariants.values()) + self.invariant_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zes.add(inv_ze)

        zss.add(z3.Not(z3.And(list(zes))))
        return zss

    def _model_to_state(self, model: z3.ModelRef, venv: VersionEnv) -> ValEnv:
        names = {venv.get_name(name): name for name in self.type_env}
        state = model_to_state(model, set(names.keys()))
        for versioned_name, name in names.items():
            state[name] = state[versioned_name]
            del state[versioned_name]
        return state

    def _uninfinite_state(self, state: ValEnv) -> Optional[ValEnv]:
        """
        state may have infinite sets and maps in it. _uninfinite_state converts
        all such sets and maps to finite python sets and maps if possible. If
        not possible, it returns None.
        """
        finite_state: ValEnv = dict()
        for k, v in state.items():
            if isinstance(v, InfiniteSet) or isinstance(v, InfiniteMap):
                if not v.finite():
                    return None
                else:
                    finite_state[k] = v.get()
            else:
                finite_state[k] = v
        return finite_state

    def _model_to_exprs(self,
                        state: ValEnv,
                        tenv: TypeEnv) \
                        -> Optional[ExprEnv]:
        finite_state = self._uninfinite_state(state)
        if finite_state is None:
            return None
        return {name: typed_coerce(x, tenv[name])
                for name, x in finite_state.items()}

    def _known_reachable(self, state: ValEnv) -> bool:
        """
        Returns whether we know that state is reachable. Note that if
        _known_reachable reachable returns false, it doesn't necessarily mean
        that state is unreachable.
        """
        finite_state = self._uninfinite_state(state)
        return (finite_state is not None and
                finite_state in self.state_explorer.states)

    def _record_state(self, state: ValEnv, label: Label) -> None:
        if label == Label.UNREACHABLE:
            self.unreachable.append(state)

            exprs = self._model_to_exprs(state, self.type_env)
            if exprs:
                inv: Expr = EBool(True)
                for name, e in exprs.items():
                    inv = EBoolAnd(inv, EVar(name).eq(e))
                self.refine_invariant(EBoolNot(inv))
        else:
            assert label == Label.REACHABLE, label
            finite_state = self._uninfinite_state(state)
            if finite_state:
                self.state_explorer.add(finite_state)

    def _is_refined_i_closed(self) -> Decision:
        with scoped(self.solver):
            # Assert lhs satisfies invariant.
            lhs_venv = VersionEnv('lhs')
            zss = self._venv_satisfies_refined_i(lhs_venv)

            # Assert rhs satisfies invariant.
            rhs_venv = VersionEnv('rhs')
            zss |= self._venv_satisfies_refined_i(rhs_venv)

            # Compute join.
            join_venv = VersionEnv('joined')
            join_zss, join_venv = compile.compile_join(
                lhs_venv, rhs_venv, join_venv, self.crdt_env, self.type_env,
                self.fresh)
            zss |= join_zss

            # Assert that the join does NOT satisfy the invariant.
            zss |= self._venv_doesnt_satisfy_refined_i(join_venv)

            # Register assertions.
            self.solver.add(list(zss))

            # Display generated code.
            if self.verbose:
                print(f'{fg(206)}{self.solver.sexpr()}{attr(0)}')

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
            # counterexample. Extract the counterexamples.
            model = self.solver.model()
            self.lhs = self._model_to_state(model, lhs_venv)
            self.rhs = self._model_to_state(model, rhs_venv)
            join = self._model_to_state(model, join_venv)

            # Check if either state is reachable. If they both are, we are
            # done.
            if self._known_reachable(self.lhs):
                self.lhs_reachable()
            if self._known_reachable(self.rhs):
                self.rhs_reachable()
            if (self.lhs_label == Label.REACHABLE and
                self.rhs_label == Label.REACHABLE):
                return Decision.NO

            # TODO(mwhittaker): Improve printing.
            m = ('The following two states (i.e. lhs and rhs) satisfy the ' +
                 '(refined) invariant, but their join does not. Please use ' +
                 'the lhs_reachable(), lhs_unreachable(), rhs_reachable(), ' +
                 'and rhs_unreachable() methods to label the states as ' +
                 'reachable or unreachable.')
            lstr = f' [{self.lhs_label}]' if self.lhs_label is not None else ''
            rstr = f' [{self.rhs_label}]' if self.rhs_label is not None else ''
            self._wrap_print(m)
            print('')
            print(f'  lhs{lstr} = {self.lhs}.')
            print(f'  rhs{rstr} = {self.rhs}.')
            print(f'  lhs join rhs = {join}.')

            return Decision.UNKNOWN

    def check(self) -> Decision:
        # Make sure that both counterexamples are labelled, if they exist.
        msg = ('State {0} is unlabelled. Call `{0}_reachable()` to label ' +
                'the state as reachable or `{0}_unreachable()` to label the ' +
                'state as unreachable.')
        if (self.lhs is not None and self.lhs_label is None):
            self._wrap_print(msg.format('lhs'))
            return Decision.UNKNOWN
        if (self.rhs is not None and self.rhs_label is None):
            self._wrap_print(msg.format('rhs'))
            return Decision.UNKNOWN

        if (self.lhs is not None):
            assert self.lhs_label is not None
            assert self.rhs is not None
            assert self.rhs_label is not None

            # Record the unreachable counterexamples. Users can use the set of
            # unreachable counterexamples to try and figure out how to refine
            # the invariant. Reachable counterexamples are stored in
            # self.state_explorer.
            self._record_state(self.lhs, self.lhs_label)
            self._record_state(self.rhs, self.rhs_label)

            # If lhs and rhs are both reachable, then so is `lhs join rhs`.
            # `lhs join rhs` does not satisfy the (refined) invariant, so if it
            # is reachable, then we are not invariant-confluent.
            if (self.lhs_label == Label.REACHABLE and
                self.rhs_label == Label.REACHABLE):
                return Decision.NO
            else:
                self.lhs = None
                self.rhs = None
                self.lhs_label = None
                self.rhs_label = None

        invs = list(self.invariants.values())
        if not self._state_satisfies_invs(self.s0_vals, invs):
            return Decision.NO
        else:
            if self.verbose:
                n = self.num_explored_states_per_step
                print(f'Exploring {n} states...')
                print('')
            self.state_explorer.explore(self.num_explored_states_per_step)
            return self._is_refined_i_closed()

    def lhs_reachable(self):
        self.lhs_label = Label.REACHABLE

    def lhs_unreachable(self):
        self.lhs_label = Label.UNREACHABLE

    def rhs_reachable(self):
        self.rhs_label = Label.REACHABLE

    def rhs_unreachable(self):
        self.rhs_label = Label.UNREACHABLE

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
