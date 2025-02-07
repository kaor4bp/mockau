from core.plain_matchers.base_plain_matcher import BasePlainMatcher
from core.plain_matchers.common_plain_matchers import CommonPlainMatcher


class BaseIntegerPlainMatcher(BasePlainMatcher):
    def is_subset(self, other):
        return self.is_intersected(other)


class IntegerEqualTo(BaseIntegerPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, IntegerEqualTo):
            return self.value == other.value
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return self.value >= other.value
        elif isinstance(other, IntegerLessOrEqualThan):
            return self.value <= other.value
        elif isinstance(other, IntegerGreaterThan):
            return self.value > other.value
        elif isinstance(other, IntegerLessThan):
            return self.value < other.value
        else:
            return other.is_intersected(self)


class IntegerGreaterThan(BaseIntegerPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return True
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return True
        elif isinstance(other, IntegerLessThan):
            return self.value < other.value
        elif isinstance(other, IntegerLessOrEqualThan):
            return self.value <= other.value
        else:
            return other.is_intersected(self)


class IntegerGreaterOrEqualThan(BaseIntegerPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return True
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return True
        elif isinstance(other, IntegerLessThan):
            return self.value < other.value
        elif isinstance(other, IntegerLessOrEqualThan):
            return self.value <= other.value
        else:
            return other.is_intersected(self)


class IntegerLessThan(BaseIntegerPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return other.value < self.value
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return other.value < self.value
        elif isinstance(other, IntegerLessThan):
            return True
        elif isinstance(other, IntegerLessOrEqualThan):
            return True
        else:
            return other.is_intersected(self)


class IntegerLessOrEqualThan(BaseIntegerPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return other.value < self.value
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return other.value <= self.value
        elif isinstance(other, IntegerLessThan):
            return True
        elif isinstance(other, IntegerLessOrEqualThan):
            return True
        else:
            return other.is_intersected(self)
