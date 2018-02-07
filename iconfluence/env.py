from typing import Dict, FrozenSet, Tuple

import z3

Version = Tuple[str, int]

class Env:
    def __init__(self, vs: FrozenSet[str], suffix: str = "") -> None:
        self.vs = vs
        self.suffix = suffix
        self.versions: Dict[str, Version] = {v: (suffix, 0) for v in self.vs}

    def __str__(self) -> str:
        return str(self.versions)

    def _copy(self) -> 'Env':
        versions_copy = self.versions.copy()
        env = Env(self.vs, self.suffix)
        env.versions = versions_copy
        return env

    def get_version(self, v: str) -> Version:
        assert v in self.versions, (v, self.versions)
        return self.versions[v]

    def get_name(self, v: str) -> str:
        (s, i) = self.get_version(v)
        i_str = f"_{i}" if i != 0 else ""
        s_str = f"_{s}" if s else ""
        return f"{v}{s_str}{i_str}"

    def with_suffix(self, suffix: str) -> 'Env':
        env = self._copy()
        env.suffix = suffix
        return env

    def assign(self, v: str) -> 'Env':
        (_, i) = self.get_version(v)
        new_version = (self.suffix, i + 1)
        env = self._copy()
        env.versions[v] = new_version
        return env
