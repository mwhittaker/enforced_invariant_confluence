class FreshName:
    """
    FreshName is used to generate fresh names that have never been used before.
    It's useful for generating fresh intermediate variables.

    >>> fresh = FreshName('foo')
    >>> fresh.get()
    x_0
    >>> fresh.get()
    x_1
    >>> fresh.get()
    x_2
    """
    def __init__(self, prefix: str = None) -> None:
        self.prefix = prefix or "_fresh_name"
        self.i = 0

    def get(self) -> str:
        s = f'{self.prefix}_{self.i}'
        self.i += 1
        return s
