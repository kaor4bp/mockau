import re

from pyformlang.regular_expression import PythonRegex

from core.plain_matchers.base_plain_matcher import BasePlainMatcher
from core.plain_matchers.common_plain_matchers import CommonPlainMatcher


class BaseStringPlainMatcher(BasePlainMatcher):
    def is_subset(self, other):
        return self.is_intersected(other)


class StringEqualTo(BaseStringPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, StringEqualTo):
            return self.value == other.value
        elif isinstance(other, StringContains):
            return bool(other.value in self.value)
        elif isinstance(other, StringPattern):
            return bool(re.fullmatch(other.pattern, self.value))
        else:
            return other.is_intersected(self)


class StringPattern(BaseStringPlainMatcher):
    def __init__(self, pattern):
        self.pattern = pattern

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, StringEqualTo):
            return bool(re.fullmatch(self.pattern, other.value))
        elif isinstance(other, StringPattern):
            regex1_dfa = PythonRegex(self.pattern).to_epsilon_nfa().minimize()
            regex2_dfa = PythonRegex(other.pattern).to_epsilon_nfa().minimize()
            intersection_1 = regex1_dfa.get_intersection(regex2_dfa)
            intersection_2 = regex2_dfa.get_intersection(regex1_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        elif isinstance(other, StringContains):
            regex1_dfa = PythonRegex(self.pattern).to_epsilon_nfa().minimize()
            regex2_dfa = PythonRegex(f'.*{other.value}.*').to_epsilon_nfa().minimize()
            intersection_1 = regex1_dfa.get_intersection(regex2_dfa)
            intersection_2 = regex2_dfa.get_intersection(regex1_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        else:
            return other.is_intersected(self)


class StringContains(BaseStringPlainMatcher):
    def __init__(self, value):
        self.value = value

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, StringEqualTo):
            return self.value in other.value
        elif isinstance(other, StringPattern):
            regex1_dfa = PythonRegex(f'.*{self.value}.*').to_epsilon_nfa().minimize()
            regex2_dfa = PythonRegex(other.pattern).to_epsilon_nfa().minimize()
            intersection_1 = regex1_dfa.get_intersection(regex2_dfa)
            intersection_2 = regex2_dfa.get_intersection(regex1_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        elif isinstance(other, StringContains):
            return True
        else:
            return other.is_intersected(self)
