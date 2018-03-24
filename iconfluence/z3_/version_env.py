from typing import Callable, Dict, FrozenSet, Tuple

import z3

Version = Tuple[str, int]

class VersionEnv:
    """
    Imagine that we have a C-like source language and that we want to compile
    to a target language in which all variables are immutable. For example,
    imagine we want to compile the following program:

        x = 0
        x = x + x
        x = 2 * x
        print(x)

    We can do so by associating the source variable x with multiple different
    target variables which act like versions of x. For example, we can compile
    this program into this one:

        x_0 = 0
        x_1 = x_0 + x_0
        x_2 = 2 * x_1
        print(x_2)

    A VersionEnv helps manage this mapping from source variable to versioned
    target variables.

    >>> venv = VersionEnv()
    >>> venv.get_name('x')
    'x_0'
    >>> venv = venv.assign('x')
    >>> venv.get_name('x')
    'x_1'
    >>> venv = venv.with_suffix('foo')
    >>> venv = venv.assign('x')
    >>> venv.get_name('x')
    'x_foo_2'
    """

    def __init__(self, suffix: str = '') -> None:
        self.suffix = suffix
        self.versions: Dict[str, Version] = dict()

    def __str__(self) -> str:
        return str(self.versions)

    def __repr__(self) -> str:
        return repr(self.versions)

    def _copy(self) -> 'VersionEnv':
        versions_copy = self.versions.copy()
        env = VersionEnv(self.suffix)
        env.versions = versions_copy
        return env

    def get_version(self, v: str) -> Version:
        if v not in self.versions:
            self.versions[v] = (self.suffix, 0)
        return self.versions[v]

    def get_name(self, v: str) -> str:
        (s, i) = self.get_version(v)
        i_str = f'_{i}'
        s_str = f'_{s}' if s else ''
        return f'{v}{s_str}{i_str}'

    def with_suffix(self, suffix: str) -> 'VersionEnv':
        env = self._copy()
        env.suffix = suffix
        return env

    def assign(self, v: str) -> 'VersionEnv':
        (_, i) = self.get_version(v)
        new_version = (self.suffix, i + 1)
        env = self._copy()
        env.versions[v] = new_version
        return env

if __name__ == '__main__':
    import doctest
    doctest.testmod()
