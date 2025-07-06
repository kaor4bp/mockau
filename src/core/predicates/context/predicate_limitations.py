from typing import Self

from pydantic import BaseModel


class PredicateLimitations(BaseModel):
    max_array_size: int = 1
    max_string_len: int = 10

    level_gte: int | None = 0
    level_lte: int | None = 0

    next: 'PredicateLimitations | None' = None
    prev: 'PredicateLimitations | None' = None

    def push(self: Self, limitation: 'PredicateLimitations') -> Self:
        if self.next is None:
            self.next = limitation._get_root()
            limitation._get_root().prev = self
        else:
            self.next.push(limitation)
        return self

    def _get_root(self):
        if self.prev is not None:
            return self.prev._get_root()
        else:
            return self

    def _get_all(self):
        limitations = [self]
        if self.next:
            limitations += self.next._get_all()
        return limitations

    def get_for_level(self, level: int) -> Self:
        all_limitations = self._get_root()._get_all()
        matched_limitations = []

        for limitation in all_limitations:
            if (limitation.level_lte is None or limitation.level_lte >= level) and (
                limitation.level_gte is None or limitation.level_gte <= level
            ):
                matched_limitations.append(limitation)

        limitation = self._union_limitations(matched_limitations)
        limitation.level_lte = level
        limitation.level_gte = level
        return limitation

    def get_max_level(self):
        cur_limit = self._get_root()
        max_level = 0
        while cur_limit:
            if cur_limit.level_lte is not None:
                max_level = max(max_level, cur_limit.level_lte)
            if cur_limit.level_gte is not None:
                max_level = max(max_level, cur_limit.level_gte)
            cur_limit = cur_limit.next

        return max_level

    def increment_level(self) -> Self:
        cur_limit = self._get_root()
        while cur_limit:
            if cur_limit.level_lte is not None:
                cur_limit.level_lte += 1
            if cur_limit.level_gte is not None:
                cur_limit.level_gte += 1
            cur_limit = cur_limit.next

        return self

    def reset_level_lte(self):
        cur_limit = self._get_root()
        while cur_limit:
            cur_limit.level_lte = None
            cur_limit = cur_limit.next

        return self

    def add_level(self):
        return self.push(PredicateLimitations(level_gte=self.get_max_level() + 1, level_lte=self.get_max_level() + 1))

    @classmethod
    def _union_limitations(cls, limitations: 'list[PredicateLimitations]') -> 'PredicateLimitations':
        limitations.append(cls())
        return cls(
            max_array_size=max([limitation.max_array_size for limitation in limitations]),
            max_string_len=max([limitation.max_string_len for limitation in limitations]),
        )
