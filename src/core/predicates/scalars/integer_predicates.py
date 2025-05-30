from typing import Literal

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseIntegerPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Integer}


class IntegerEqualTo(BaseIntegerPredicate):
    type_of: Literal['IntegerEqualTo'] = 'IntegerEqualTo'
    value: int

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var == self.value


class IntegerGreaterThan(BaseIntegerPredicate):
    type_of: Literal['IntegerGreaterThan'] = 'IntegerGreaterThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var > self.value


class IntegerGreaterOrEqualThan(BaseIntegerPredicate):
    type_of: Literal['IntegerGreaterOrEqualThan'] = 'IntegerGreaterOrEqualThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var >= self.value


class IntegerLessThan(BaseIntegerPredicate):
    type_of: Literal['IntegerLessThan'] = 'IntegerLessThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var < self.value


class IntegerLessOrEqualThan(BaseIntegerPredicate):
    type_of: Literal['IntegerLessOrEqualThan'] = 'IntegerLessOrEqualThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return var <= self.value
