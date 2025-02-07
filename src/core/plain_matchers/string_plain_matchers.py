import re
from functools import cached_property
from typing import Annotated, Literal, Union

from pydantic import Field
from pyformlang.regular_expression import PythonRegex

from core.plain_matchers.base_plain_matcher import (
    BaseAndPlainMatcher,
    BaseAnyPlainMatcher,
    BaseNotPlainMatcher,
    BaseOrPlainMatcher,
    BasePlainMatcher,
)


class BaseStringPlainMatcher(BasePlainMatcher):
    def is_subset(self, other):
        return self.is_intersected(other)


class StringEqualTo(BaseStringPlainMatcher):
    type_of: Literal['StringEqualTo'] = 'StringEqualTo'
    value: str

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            return self.value == other.value
        elif isinstance(other, StringContains):
            return bool(other.value in self.value)
        elif isinstance(other, StringPattern):
            return bool(re.fullmatch(other.pattern, self.value))
        else:
            return other.is_intersected(self)


class StringPattern(BaseStringPlainMatcher):
    type_of: Literal['StringPattern'] = 'StringPattern'
    pattern: str

    @cached_property
    def pattern_dfa(self):
        return PythonRegex(self.pattern).to_epsilon_nfa().minimize()

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            return re.fullmatch(self.pattern, other.value)
        elif isinstance(other, StringPattern):
            intersection_1 = self.pattern_dfa.get_intersection(other.pattern_dfa)
            intersection_2 = other.pattern_dfa.get_intersection(self.pattern_dfa)
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
    type_of: Literal['StringContains'] = 'StringContains'
    value: str

    @cached_property
    def pattern_dfa(self):
        return PythonRegex(f'.*{self.value}.*').to_epsilon_nfa().minimize()

    def is_intersected(self, other):
        assert isinstance(other, BaseStringPlainMatcher)

        if isinstance(other, StringEqualTo):
            return self.value in other.value
        elif isinstance(other, StringPattern):
            intersection_1 = self.pattern_dfa.get_intersection(other.pattern_dfa)
            intersection_2 = other.pattern_dfa.get_intersection(self.pattern_dfa)
            return bool(not intersection_1.is_empty() or not intersection_2.is_empty())
        elif isinstance(other, StringContains):
            return True
        else:
            return other.is_intersected(self)


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
