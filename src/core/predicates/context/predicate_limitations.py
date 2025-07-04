from typing import Self

from pydantic import BaseModel


class PredicateLimitations(BaseModel):
    max_nesting_level: int = 0
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
        limitation.max_nesting_level = self.get_max_level() - level + 1
        return limitation

    def get_max_level(self):
        cur_limit = self._get_root()
        max_level = 0
        while cur_limit:
            if cur_limit.level_lte is not None:
                max_level = max(max_level, cur_limit.level_lte + self.max_nesting_level)
            if cur_limit.level_gte is not None:
                max_level = max(max_level, cur_limit.level_gte + self.max_nesting_level)
            # max_level = max(max_level, self.max_nesting_level + self.level_gte)
            cur_limit = cur_limit.next

        return max_level

    def increment_level(self, reset_level_lte: bool = False) -> Self:
        cur_limit = self._get_root()
        while cur_limit:
            if cur_limit.level_lte is not None:
                cur_limit.level_lte += 1
            if cur_limit.level_gte is not None:
                cur_limit.level_gte += 1
            if reset_level_lte:
                cur_limit.level_lte = None
            cur_limit.max_nesting_level += 1
            cur_limit = cur_limit.next

        return self

    @classmethod
    def _union_limitations(cls, limitations: 'list[PredicateLimitations]') -> 'PredicateLimitations':
        limitations.append(cls())
        return cls(
            max_nesting_level=max([limitation.max_nesting_level for limitation in limitations]),
            max_array_size=max([limitation.max_array_size for limitation in limitations]),
            max_string_len=max([limitation.max_string_len for limitation in limitations]),
        )
