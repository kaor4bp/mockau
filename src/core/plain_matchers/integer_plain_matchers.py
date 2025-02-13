from typing import Annotated, Literal, Union

from pydantic import Field

from core.plain_matchers.base_plain_matcher import (
    BaseAndPlainMatcher,
    BaseAnyPlainMatcher,
    BaseNotPlainMatcher,
    BaseOrPlainMatcher,
    BasePlainMatcher,
)


class BaseIntegerPlainMatcher(BasePlainMatcher):
    def is_subset_of(self, other):
        return self.is_intersected_with(other)


class IntegerEqualTo(BaseIntegerPlainMatcher):
    type_of: Literal['IntegerEqualTo'] = 'IntegerEqualTo'
    value: int

    def is_intersected_with(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher)

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
            return other.is_intersected_with(self)


class IntegerGreaterThan(BaseIntegerPlainMatcher):
    type_of: Literal['IntegerGreaterThan'] = 'IntegerGreaterThan'
    value: int

    def is_intersected_with(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return True
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return True
        elif isinstance(other, IntegerLessThan):
            return self.value < other.value
        elif isinstance(other, IntegerLessOrEqualThan):
            return self.value <= other.value
        else:
            return other.is_intersected_with(self)


class IntegerGreaterOrEqualThan(BaseIntegerPlainMatcher):
    type_of: Literal['IntegerGreaterOrEqualThan'] = 'IntegerGreaterOrEqualThan'
    value: int

    def is_intersected_with(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return True
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return True
        elif isinstance(other, IntegerLessThan):
            return self.value < other.value
        elif isinstance(other, IntegerLessOrEqualThan):
            return self.value <= other.value
        else:
            return other.is_intersected_with(self)


class IntegerLessThan(BaseIntegerPlainMatcher):
    type_of: Literal['IntegerLessThan'] = 'IntegerLessThan'
    value: int

    def is_intersected_with(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return other.value < self.value
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return other.value < self.value
        elif isinstance(other, IntegerLessThan):
            return True
        elif isinstance(other, IntegerLessOrEqualThan):
            return True
        else:
            return other.is_intersected_with(self)


class IntegerLessOrEqualThan(BaseIntegerPlainMatcher):
    type_of: Literal['IntegerLessOrEqualThan'] = 'IntegerLessOrEqualThan'
    value: int

    def is_intersected_with(self, other):
        assert isinstance(other, BaseIntegerPlainMatcher)

        if isinstance(other, IntegerGreaterThan):
            return other.value < self.value
        elif isinstance(other, IntegerGreaterOrEqualThan):
            return other.value <= self.value
        elif isinstance(other, IntegerLessThan):
            return True
        elif isinstance(other, IntegerLessOrEqualThan):
            return True
        else:
            return other.is_intersected_with(self)


class IntegerAny(BaseIntegerPlainMatcher, BaseAnyPlainMatcher):
    type_of: Literal['IntegerAny'] = 'IntegerAny'


class IntegerNot(BaseIntegerPlainMatcher, BaseNotPlainMatcher['_t_IntegerPlainMatcher']):
    type_of: Literal['IntegerNot'] = 'IntegerNot'


class IntegerAnd(BaseIntegerPlainMatcher, BaseAndPlainMatcher['_t_IntegerPlainMatcher']):
    type_of: Literal['IntegerAnd'] = 'IntegerAnd'


class IntegerOr(BaseIntegerPlainMatcher, BaseOrPlainMatcher['_t_IntegerPlainMatcher']):
    type_of: Literal['IntegerOr'] = 'IntegerOr'


_t_IntegerPlainMatcher = Annotated[
    Union[
        IntegerEqualTo,
        IntegerGreaterThan,
        IntegerGreaterOrEqualThan,
        IntegerLessThan,
        IntegerLessOrEqualThan,
        IntegerAny,
        IntegerNot,
        IntegerAnd,
        IntegerOr,
    ],
    Field(discriminator='type_of'),
]
IntegerAny.model_rebuild()
IntegerNot.model_rebuild()
IntegerAnd.model_rebuild()
IntegerOr.model_rebuild()
