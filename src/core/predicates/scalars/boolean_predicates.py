from typing import Literal

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseBooleanPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Boolean}


class BooleanEqualTo(BaseBooleanPredicate):
    type_of: Literal['BooleanEqualTo'] = 'BooleanEqualTo'
    value: bool

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        return ctx.create_typed_constraint(var == self.value, self.predicate_type)
