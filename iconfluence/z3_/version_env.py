from typing import Callable, Dict, FrozenSet, Tuple

import z3

Version = Tuple[str, int]

class VersionEnv:
    """
    TODO(mwhittaker): Document.
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

    def rename(self, f: Callable[[str], str]) -> 'VersionEnv':
        env = self._copy()
        names = list(env.versions.keys())
        for name in names:
            new_name = f(name)
            assert new_name not in names, (new_name, names)
            env.versions[new_name] = env.versions[name]
            del env.versions[name]
        return env

    def update(self, other: 'VersionEnv') -> 'VersionEnv':
        # Assert that variable names are disjoint.
        my_keys = set(self.versions.keys())
        other_keys = set(other.versions.keys())
        assert my_keys.isdisjoint(other_keys), (my_keys, other_keys)

        env = self._copy()
        env.versions.update(other.versions)
        return env

if __name__ == '__main__':
    import doctest
    doctest.testmod()
