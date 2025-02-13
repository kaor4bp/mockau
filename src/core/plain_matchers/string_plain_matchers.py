import re
from functools import cached_property
from typing import Annotated, Literal, Union

import exrex
from pydantic import Field
from pyformlang.finite_automaton import EpsilonNFA
from pyformlang.regular_expression import PythonRegex

from core.plain_matchers.base_plain_matcher import (
    BaseAndPlainMatcher,
    BaseAnyPlainMatcher,
    BaseNotPlainMatcher,
    BaseOrPlainMatcher,
    BasePlainMatcher,
)


def is_pattern_equal_to_string(value: str, pattern: str) -> bool:
    return all(value == generated_value for generated_value in exrex.generate(pattern))


class BaseStringPlainMatcher(BasePlainMatcher):
    def is_subset_of(self, other):
        if isinstance(other, StringAny):
            return True
        elif isinstance(other, StringNot):
            return not self.is_subset_of(other.matcher)
        elif isinstance(other, StringAnd):
            for matcher in other.matchers:
                if not self.is_subset_of(matcher):
                    return False
            else:
                return True
        elif isinstance(other, StringOr):
            for matcher in other.matchers:
                if self.is_subset_of(matcher):
                    return True
            else:
                return False
        else:
            raise AssertionError('Unsupported')


class StringEqualTo(BaseStringPlainMatcher):
    type_of: Literal['StringEqualTo'] = 'StringEqualTo'
    value: str
    ignore_case: bool = False

    def is_matched(self, value: str) -> bool:
        if self.ignore_case:
            return value.lower() == self.value.lower()
        else:
            return value == self.value

    def is_subset_of(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            if other.ignore_case:
                return self.value.lower() == other.value.lower()
            else:
                return self.value == other.value
        elif isinstance(other, StringContains):
            if other.ignore_case:
                return bool(other.value.lower() in self.value.lower())
            else:
                return bool(other.value in self.value)
        elif isinstance(other, StringPattern):
            if other.ignore_case:
                return bool(re.fullmatch(other.pattern.lower(), self.value, re.IGNORECASE))
            else:
                return bool(re.fullmatch(other.pattern, self.value))
        else:
            return super().is_subset_of(other)

    def is_intersected_with(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            if self.ignore_case or other.ignore_case:
                return self.value.lower() == other.value.lower()
            else:
                return self.value == other.value
        elif isinstance(other, StringContains):
            if self.ignore_case or other.ignore_case:
                return bool(other.value.lower() in self.value.lower())
            else:
                return bool(other.value in self.value)
        elif isinstance(other, StringPattern):
            if self.ignore_case or other.ignore_case:
                return bool(re.fullmatch(other.pattern.lower(), self.value, re.IGNORECASE))
            else:
                return bool(re.fullmatch(other.pattern, self.value))
        else:
            return other.is_intersected_with(self)


class StringPattern(BaseStringPlainMatcher):
    type_of: Literal['StringPattern'] = 'StringPattern'
    pattern: str
    ignore_case: bool = False

    def is_matched(self, value: str) -> bool:
        if self.ignore_case:
            return bool(re.fullmatch(self.pattern.lower(), value, re.IGNORECASE))
        else:
            return bool(re.fullmatch(self.pattern, value))

    @cached_property
    def pattern_dfa(self) -> EpsilonNFA:
        return PythonRegex(self.pattern).to_epsilon_nfa().minimize()

    @cached_property
    def case_insensitive_pattern_dfa(self):
        return PythonRegex(self.pattern.lower()).to_epsilon_nfa().minimize()

    def is_subset_of(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            if other.ignore_case:
                return bool(
                    re.fullmatch(self.pattern.lower(), other.value, re.IGNORECASE)
                    and is_pattern_equal_to_string(other.value, self.pattern)
                )
            else:
                return bool(
                    re.fullmatch(self.pattern, other.value) and is_pattern_equal_to_string(self.pattern, other.value)
                )
        elif isinstance(other, StringPattern):
            if other.ignore_case:
                difference = self.case_insensitive_pattern_dfa.get_difference(other.case_insensitive_pattern_dfa)
            else:
                difference = self.pattern_dfa.get_difference(other.pattern_dfa)
            return bool(difference.is_empty())
        elif isinstance(other, StringContains):
            if other.ignore_case:
                difference = self.case_insensitive_pattern_dfa.get_difference(other.case_insensitive_pattern_dfa)
            else:
                difference = self.pattern_dfa.get_difference(other.pattern_dfa)
            return bool(difference.is_empty())
        else:
            return super().is_subset_of(other)

    def is_intersected_with(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            if self.ignore_case or other.ignore_case:
                return bool(re.fullmatch(self.pattern.lower(), other.value, re.IGNORECASE))
            else:
                return bool(re.fullmatch(self.pattern, other.value))
        elif isinstance(other, StringPattern):
            if self.ignore_case or other.ignore_case:
                intersection_1 = self.case_insensitive_pattern_dfa.get_intersection(other.case_insensitive_pattern_dfa)
                intersection_2 = other.case_insensitive_pattern_dfa.get_intersection(self.case_insensitive_pattern_dfa)
            else:
                intersection_1 = self.pattern_dfa.get_intersection(other.pattern_dfa)
                intersection_2 = other.pattern_dfa.get_intersection(self.pattern_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        elif isinstance(other, StringContains):
            if self.ignore_case or other.ignore_case:
                intersection_1 = self.case_insensitive_pattern_dfa.get_intersection(other.case_insensitive_pattern_dfa)
                intersection_2 = other.case_insensitive_pattern_dfa.get_intersection(self.case_insensitive_pattern_dfa)
            else:
                intersection_1 = self.pattern_dfa.get_intersection(other.pattern_dfa)
                intersection_2 = other.pattern_dfa.get_intersection(self.pattern_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        else:
            return other.is_intersected_with(self)


class StringContains(BaseStringPlainMatcher):
    type_of: Literal['StringContains'] = 'StringContains'
    value: str
    ignore_case: bool = False

    def is_matched(self, value: str) -> bool:
        if self.ignore_case:
            return self.value.lower() in value.lower()
        else:
            return self.value in value

    @cached_property
    def pattern_dfa(self):
        return PythonRegex(f'.*{self.value}.*').to_epsilon_nfa().minimize()

    @cached_property
    def case_insensitive_pattern_dfa(self):
        return PythonRegex(f'.*{self.value.lower()}.*').to_epsilon_nfa().minimize()

    def is_subset_of(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            return False
        elif isinstance(other, StringPattern):
            if other.ignore_case:
                intersection = self.case_insensitive_pattern_dfa.get_intersection(other.case_insensitive_pattern_dfa)
            else:
                intersection = self.pattern_dfa.get_intersection(other.pattern_dfa)
            return bool(not intersection.is_empty())
        elif isinstance(other, StringContains):
            if other.ignore_case:
                return self.value.lower() == other.value.lower()
            else:
                return self.value == other.value
        else:
            return super().is_subset_of(other)

    def is_intersected_with(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            if self.ignore_case or other.ignore_case:
                return self.value.lower() in other.value.lower()
            else:
                return self.value in other.value
        elif isinstance(other, StringPattern):
            if self.ignore_case or other.ignore_case:
                intersection_1 = self.case_insensitive_pattern_dfa.get_intersection(other.case_insensitive_pattern_dfa)
                intersection_2 = other.case_insensitive_pattern_dfa.get_intersection(self.case_insensitive_pattern_dfa)
            else:
                intersection_1 = self.pattern_dfa.get_intersection(other.pattern_dfa)
                intersection_2 = other.pattern_dfa.get_intersection(self.pattern_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        elif isinstance(other, StringContains):
            return True
        else:
            return other.is_intersected_with(self)


class StringAny(BaseStringPlainMatcher, BaseAnyPlainMatcher):
    type_of: Literal['StringAny'] = 'StringAny'


class StringNot(BaseStringPlainMatcher, BaseNotPlainMatcher['_t_StringPlainMatcher']):
    type_of: Literal['StringNot'] = 'StringNot'


class StringAnd(BaseStringPlainMatcher, BaseAndPlainMatcher['_t_StringPlainMatcher']):
    type_of: Literal['StringAnd'] = 'StringAnd'


class StringOr(BaseStringPlainMatcher, BaseOrPlainMatcher['_t_StringPlainMatcher']):
    type_of: Literal['StringOr'] = 'StringOr'


_t_StringPlainMatcher = Annotated[
    Union[
        StringEqualTo,
        StringPattern,
        StringContains,
        StringAny,
        StringNot,
        StringAnd,
        StringOr,
    ],
    Field(discriminator='type_of'),
]

StringAny.model_rebuild()
StringNot.model_rebuild()
StringAnd.model_rebuild()
StringOr.model_rebuild()
