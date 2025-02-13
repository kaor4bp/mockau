import re
from typing import Self

from pydantic import ValidationError, model_validator

from core.matchers.variable_matcher import SetVariableMatcher
from core.plain_matchers.integer_plain_matchers import (
    IntegerAnd,
    IntegerAny,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNot,
    IntegerOr,
)
from core.plain_matchers.types import t_IntegerPlainMatcher, t_PlainMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class IntegerMatcher(SetVariableMatcher):
    equal_to: int | None = None
    gte: int | None = None
    gt: int | None = None
    lte: int | None = None
    lt: int | None = None

    and_: list['IntegerMatcher'] | None = None
    or_: list['IntegerMatcher'] | None = None
    not_: 'IntegerMatcher | None' = None

    @model_validator(mode='after')
    def sort_items(self: Self) -> Self:
        if self.set_variable and re.fullmatch(r'\${\w+}', self.set_variable) is None:
            raise ValidationError('Using of patterns for set_variable in IntegerMatcher is prohibited')
        return self

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        plain_matchers = []

        if self.equal_to:
            plain_matchers.append(IntegerEqualTo(value=self.equal_to))
        if self.gte is not None:
            plain_matchers.append(IntegerGreaterOrEqualThan(value=self.gte))
        if self.gt is not None:
            plain_matchers.append(IntegerGreaterThan(value=self.gt))
        if self.lte is not None:
            plain_matchers.append(IntegerLessOrEqualThan(value=self.lte))
        if self.lt is not None:
            plain_matchers.append(IntegerLessThan(value=self.lt))
        if self.and_:
            plain_matchers.append(
                IntegerAnd(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.and_])
            )
        if self.or_:
            plain_matchers.append(
                IntegerOr(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.or_])
            )
        if self.not_:
            plain_matchers.append(
                IntegerNot[t_IntegerPlainMatcher](matcher=self.not_.to_plain_matcher(context=context))
            )

        if len(plain_matchers) == 0:
            return IntegerAny()
        elif len(plain_matchers) == 1:
            return plain_matchers[0]
        else:
            return IntegerAnd(matchers=plain_matchers)

    @variables_context_transaction
    def is_matched(self, value: int, *, context: VariablesContext) -> bool:
        return self.to_plain_matcher(context=context).is_matched(value)


t_IntegerMatcher = IntegerMatcher
