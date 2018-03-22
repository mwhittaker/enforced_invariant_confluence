from enum import Enum
from typing import List, Optional, Tuple

from orderedset import OrderedSet
import z3

from ..ast import EVar, Expr, Invariant
from ..checker import Checker, Decision
from ..envs import ValEnv, TypeEnv, Z3ExprEnv
from ..eval import eval_invariant
from ..state_explorer import StateExplorer
from ..typecheck import typecheck_invariant
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
    >>> checker.check_iconfluence()
    Counterexample found.
    lhs = {'x': 0, 'y': 1}.
    rhs = {'x': 1, 'y': 0}.
    <Decision.UNKNOWN: 'unknown'>
    >>> checker.lhs_unreachable()
    >>> checker.rhs_reachable()
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
        self.unreachable_z3: List[Z3ExprEnv] = []
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

            l1_str = f' [{self.lhs_label}]' if self.lhs_label is not None else ''
            l2_str = f' [{self.rhs_label}]' if self.rhs_label is not None else ''
            strings.append(f'  counterexample 1 == {self.lhs}{l1_str}')
            strings.append(f'  counterexample 2 == {self.rhs}{l2_str}')

        return '\n'.join([Checker.__str__(self)] + strings)

    def _record_if_unreachable(self, \
                               counterexample: Z3ExprEnv, \
                               label: Label) \
                               -> None:
        if label == Label.UNREACHABLE:
            self.unreachable_z3.append(counterexample)

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

    def _known_reachable(self, state: ValEnv) -> bool:
        """
        Returns whether we know that state is reachable. Note that if
        _known_reachable reachable returns false, it doesn't necessarily mean
        that state is unreachable.
        """
        finite_state = self._uninfinite_state(state)
        return (finite_state is not None and
                finite_state in self.state_explorer.states)

    def _is_refined_i_closed(self) -> Decision:
        with scoped(self.solver):
            # Assert rhs satisfies invariant.
            lhs_venv = VersionEnv('lhs')
            zss = self._venv_satisfies_refined_i(lhs_venv)

            # Assert lhs satisfies invariant.
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
            print('The following two states (i.e. lhs and rhs) satisfy the ' +
                  '(refined) invariant, but their join does not. Please use ' +
                  'the lhs_reachable(), lhs_unreachable(), rhs_reachable(), ' +
                  'and rhs_unreachable() methods to label the states as ' +
                  'reachable or unreachable.')
            print(f'lhs [{self.lhs_label}] = {self.lhs}.')
            print(f'rhs [{self.rhs_label}] = {self.rhs}.')
            print(f'lhs join rhs = {join}.')

            return Decision.UNKNOWN

    def check_iconfluence(self) -> Decision:
        # Make sure that both counterexamples are labelled, if they exist.
        msg = ('State {0} is unlabelled. Call `{0}_reachable()` to label ' +
                'the state as reachable or `{0}_unreachable()` to label the ' +
                'state as unreachable.')
        if (self.lhs is not None and self.lhs_label is None):
            print(msg.format('lhs'))
            return Decision.UNKNOWN
        if (self.rhs is not None and self.rhs_label is None):
            print(msg.format('rhs'))
            return Decision.UNKNOWN

        if (self.lhs is not None):
            assert self.lhs_label is not None
            assert self.rhs is not None
            assert self.rhs_label is not None

            # Record the unreachable counterexamples. Users can use the set of
            # unreachable counterexamples to try and figure out how to refine
            # the invariant. Reachable counterexamples are stored in
            # self.state_explorer.
            self._record_if_unreachable(self.lhs, self.lhs_label)
            self._record_if_unreachable(self.rhs, self.rhs_label)

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
                print(f'Exploring {self.num_explored_states_per_step} states.')
            self.state_explorer.explore(self.num_explored_states_per_step)
            return self._is_refined_i_closed()

    def lhs_reachable(self):
        self.lhs_label = Label.REACHABLE
        # TODO(mwhittaker): Update in check_invariant_confluence.
        finite_state = self._uninfinite_state(self.lhs)
        if finite_state:
            self.state_explorer.add(finite_state)

    def lhs_unreachable(self):
        self.lhs_label = Label.UNREACHABLE
        # TODO(mwhittaker): Refine invariant.

    def rhs_reachable(self):
        self.rhs_label = Label.REACHABLE
        # TODO(mwhittaker): Remove boilerplate.
        finite_state = self._uninfinite_state(self.rhs)
        if finite_state:
            self.state_explorer.add(finite_state)

    def rhs_unreachable(self):
        self.rhs_label = Label.UNREACHABLE
        # TODO(mwhittaker): Refine invariant.

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
