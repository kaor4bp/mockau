from abc import abstractmethod
from copy import deepcopy
from typing import Generic, TypeVar

from core.bases.base_schema import BaseSchema


class BasePlainMatcher(BaseSchema):
    @abstractmethod
    def is_intersected(self, other):
        pass

    @abstractmethod
    def is_subset(self, other):
        pass


_t_PlainMatcher = TypeVar('_t_PlainMatcher', bound=BasePlainMatcher)


class BaseAnyPlainMatcher(BasePlainMatcher):
    def is_intersected(self, other):
        return True

    def is_subset(self, other):
        return True


class BaseNotPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matcher: _t_PlainMatcher

    def is_intersected(self, other):
        return not self.matcher.is_intersected(other)

    def is_subset(self, other):
        return not self.matcher.is_subset(other)


class BaseAndPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matchers: list[_t_PlainMatcher]

    def is_subset(self, other):
        if isinstance(other, BaseAndPlainMatcher):
            other_matchers = list(deepcopy(other.matchers))
            for matcher in self.matchers:
                is_found = False
                for other_matcher_index, other_matcher in enumerate(other_matchers):
                    if matcher.is_subset(other_matcher):
                        is_found = True
                        other_matchers.pop(other_matcher_index)
                        break
                if not is_found:
                    return False
            return True
        elif isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_subset(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_subset(other) for matcher in self.matchers)

    def is_intersected(self, other):
        if isinstance(other, BaseAndPlainMatcher):
            other_matchers = list(deepcopy(other.matchers))
            for matcher in self.matchers:
                is_found = False
                for other_matcher_index, other_matcher in enumerate(other_matchers):
                    if matcher.is_intersected(other_matcher):
                        is_found = True
                        other_matchers.pop(other_matcher_index)
                        break
                if not is_found:
                    return False
            return True
        elif isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_intersected(other) for matcher in self.matchers)


class BaseOrPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matchers: list[_t_PlainMatcher]

    def is_subset(self, other):
        if isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected(other) for matcher in self.matchers)

    def is_intersected(self, other):
        if isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected(other) for matcher in self.matchers)
