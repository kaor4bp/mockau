from copy import deepcopy

from core.plain_matchers.base_plain_matcher import BasePlainMatcher


class CommonPlainMatcher(BasePlainMatcher):
    pass


class Any(CommonPlainMatcher):
    def is_intersected(self, other):
        return True

    def is_subset(self, other):
        return True


class Not(CommonPlainMatcher):
    def __init__(self, matcher):
        self.matcher = matcher

    def is_intersected(self, other):
        return not self.matcher.is_intersected(other)

    def is_subset(self, other):
        return not self.matcher.is_subset(other)


class And(CommonPlainMatcher):
    def __init__(self, *matchers):
        self.matchers = matchers

    def is_subset(self, other):
        if isinstance(other, And):
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
        elif isinstance(other, Or):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_subset(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_subset(other) for matcher in self.matchers)

    def is_intersected(self, other):
        if isinstance(other, And):
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
        elif isinstance(other, Or):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return all(matcher.is_intersected(other) for matcher in self.matchers)


class Or(CommonPlainMatcher):
    def __init__(self, *matchers):
        self.matchers = matchers

    def is_subset(self, other):
        if isinstance(other, Or):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected(other) for matcher in self.matchers)

    def is_intersected(self, other):
        if isinstance(other, Or):
            for matcher in self.matchers:
                for other_matcher in other.matchers:
                    if matcher.is_intersected(other_matcher):
                        return True
            return False
        else:
            return any(matcher.is_intersected(other) for matcher in self.matchers)
