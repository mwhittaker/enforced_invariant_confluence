from typing import Dict, Optional

class FreshName:
    """
    FreshName is used to generate fresh names that have never been used before.
    It's useful for generating fresh intermediate variables.

    >>> fresh = FreshName('default')
    >>> fresh.get()
    __default_0
    >>> fresh.get()
    __default_1
    >>> fresh.get('foo')
    __foo_0
    >>> fresh.get('foo')
    __foo_1
    """
    def __init__(self, prefix: str = None) -> None:
        self.prefix = prefix or "__fresh_name"
        self.ids: Dict[str, int] = {self.prefix: 0}

    def get(self, prefix: Optional[str] = None) -> str:
        prefix = prefix or self.prefix
        if prefix not in self.ids:
            self.ids[prefix] = 0

        i = self.ids[prefix]
        s = f'__{prefix}_{i}'
        self.ids[prefix] += 1
        return s
