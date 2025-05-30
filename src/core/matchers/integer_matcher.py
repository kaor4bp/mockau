import re
from typing import Self

from pydantic import ValidationError, model_validator

from core.matchers.variable_matcher import SetVariableMatcher
from core.predicates.base_predicate import t_Predicate
from core.predicates.logical.logical_predicates import AndPredicate, AnyPredicate, NotPredicate, OrPredicate
from core.predicates.scalars import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
)
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

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        predicates = []

        if self.equal_to:
            predicates.append(IntegerEqualTo(value=self.equal_to))
        if self.gte is not None:
            predicates.append(IntegerGreaterOrEqualThan(value=self.gte))
        if self.gt is not None:
            predicates.append(IntegerGreaterThan(value=self.gt))
        if self.lte is not None:
            predicates.append(IntegerLessOrEqualThan(value=self.lte))
        if self.lt is not None:
            predicates.append(IntegerLessThan(value=self.lt))
        if self.and_:
            predicates.append(AndPredicate(predicates=[matcher.to_predicate(context=context) for matcher in self.and_]))
        if self.or_:
            predicates.append(OrPredicate(predicates=[matcher.to_predicate(context=context) for matcher in self.or_]))
        if self.not_:
            predicates.append(NotPredicate(predicate=self.not_.to_predicate(context=context)))

        if len(predicates) == 0:
            return AnyPredicate()
        elif len(predicates) == 1:
            return predicates[0]
        else:
            return AndPredicate(predicates=predicates)

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
