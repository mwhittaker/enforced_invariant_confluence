class FreshName:
    def __init__(self, prefix: str = None) -> None:
        self.prefix = prefix or "_fresh_name"
        self.i = 0

    def get(self) -> str:
        s = f'{self.prefix}_{self.i}'
        self.i += 1
        return s
