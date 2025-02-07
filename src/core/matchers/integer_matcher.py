import re
from typing import Self

from pydantic import ValidationError, model_validator

from core.matchers.variable_matcher import SetVariableMatcher
from core.plain_matchers.common_plain_matchers import And, Any, Not, Or
from core.plain_matchers.integer_plain_matchers import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
)
from core.plain_matchers.types import t_PlainMatcher
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
            plain_matchers.append(IntegerEqualTo(self.equal_to))
        if self.gte is not None:
            plain_matchers.append(IntegerGreaterOrEqualThan(self.gte))
        if self.gt is not None:
            plain_matchers.append(IntegerGreaterThan(self.gt))
        if self.lte is not None:
            plain_matchers.append(IntegerLessOrEqualThan(self.lte))
        if self.lt is not None:
            plain_matchers.append(IntegerLessThan(self.lt))
        if self.and_:
            plain_matchers.append(And(*[matcher.to_plain_matcher(context=context) for matcher in self.and_]))
        if self.or_:
            plain_matchers.append(Or(*[matcher.to_plain_matcher(context=context) for matcher in self.or_]))
        if self.not_:
            plain_matchers.append(Not(self.not_.to_plain_matcher(context=context)))

        if len(plain_matchers) == 0:
            return Any()
        elif len(plain_matchers) == 1:
            return plain_matchers[0]
        else:
            return And(*plain_matchers)

    @variables_context_transaction
    def is_matched(self, value: int, *, context: VariablesContext) -> bool:
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.gte is not None and value < self.gte:
            return False
        if self.gt is not None and value <= self.gt:
            return False
        if self.lte is not None and value > self.lte:
            return False
        if self.lt is not None and value >= self.lt:
            return False
        if self.and_ and any(not item.is_matched(value, context=context) for item in self.and_):
            return False
        if self.or_ and all(not item.is_matched(value, context=context) for item in self.or_):
            return False
        if self.not_ and self.not_.is_matched(value, context=context):
            return False
        if self.set_variable is not None and not self.is_variable_matched(value, context=context):
            return False
        return True


t_IntegerMatcher = IntegerMatcher
