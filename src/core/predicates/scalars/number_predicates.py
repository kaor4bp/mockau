from typing import Literal

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseNumberPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Real}


class NumberEqualTo(BaseNumberPredicate):
    type_of: Literal['NumberEqualTo'] = 'NumberEqualTo'
    value: float

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var == self.value


class NumberGreaterThan(BaseNumberPredicate):
    type_of: Literal['NumberGreaterThan'] = 'NumberGreaterThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var > self.value


class NumberGreaterOrEqualThan(BaseNumberPredicate):
    type_of: Literal['NumberGreaterOrEqualThan'] = 'NumberGreaterOrEqualThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var >= self.value


class NumberLessThan(BaseNumberPredicate):
    type_of: Literal['NumberLessThan'] = 'NumberLessThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var < self.value


class NumberLessOrEqualThan(BaseNumberPredicate):
    type_of: Literal['NumberLessOrEqualThan'] = 'NumberLessOrEqualThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var <= self.value
