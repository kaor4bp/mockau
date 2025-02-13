from abc import abstractmethod
from copy import deepcopy
from typing import Generic, TypeVar

from core.bases.base_schema import BaseSchema


class BasePlainMatcher(BaseSchema):
    def __hash__(self):
        return self.model_dump_json().__hash__()

    @abstractmethod
    def is_intersected_with(self, other):
        pass

    @abstractmethod
    def is_subset_of(self, other):
        pass

    def is_equivalent_to(self, other):
        if not self.is_intersected_with(other):
            return False

        is_self_is_subset = self.is_subset_of(other)
        is_other_is_subset = other.is_subset_of(self)

        if is_self_is_subset and is_other_is_subset:
            return True
        else:
            return False

    def is_superset_of(self, other):
        if not self.is_intersected_with(other):
            return False

        is_self_is_subset = self.is_subset_of(other)
        is_other_is_subset = other.is_subset_of(self)

        if is_self_is_subset and not is_other_is_subset:
            return False
        else:
            return True


_t_PlainMatcher = TypeVar('_t_PlainMatcher', bound=BasePlainMatcher)


class BaseAnyPlainMatcher(BasePlainMatcher):
    def is_intersected_with(self, other):
        return True

    def is_subset_of(self, other):
        return True


class BaseNotPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matcher: _t_PlainMatcher

    def is_intersected_with(self, other):
        return not self.matcher.is_intersected_with(other)

    def is_subset_of(self, other):
        return not self.matcher.is_subset_of(other)


class BaseAndPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matchers: list[_t_PlainMatcher]

    def is_subset_of(self, other):
        if isinstance(other, BaseAndPlainMatcher):
            other_matchers = list(deepcopy(other.matchers))
            for matcher in self.matchers:
                is_found = False
                for other_matcher_index, other_matcher in enumerate(other_matchers):
                    if matcher.is_subset_of(other_matcher):
                        is_found = True
                        other_matchers.pop(other_matcher_index)
                        break
                if not is_found:
                    return False
            return True
        elif isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_subset_of(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_subset_of(other) for matcher in self.matchers)

    def is_intersected_with(self, other):
        if isinstance(other, BaseAndPlainMatcher):
            other_matchers = list(deepcopy(other.matchers))
            for matcher in self.matchers:
                is_found = False
                for other_matcher_index, other_matcher in enumerate(other_matchers):
                    if matcher.is_intersected_with(other_matcher):
                        is_found = True
                        other_matchers.pop(other_matcher_index)
                        break
                if not is_found:
                    return False
            return True
        elif isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected_with(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_intersected_with(other) for matcher in self.matchers)


class BaseOrPlainMatcher(BasePlainMatcher, Generic[_t_PlainMatcher]):
    matchers: list[_t_PlainMatcher]

    def is_subset_of(self, other):
        if isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected_with(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected_with(other) for matcher in self.matchers)

    def is_intersected_with(self, other):
        if isinstance(other, BaseOrPlainMatcher):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected_with(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected_with(other) for matcher in self.matchers)
