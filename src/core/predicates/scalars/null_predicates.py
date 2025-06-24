from typing import Literal

import z3

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseNullPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Null}


class IsNull(BaseNullPredicate):
    type_of: Literal['IsNull'] = 'IsNull'

    def __invert__(self):
        return IsNotNull()

    def to_z3(self, ctx: VariableContext):
        ctx.get_variable(self.predicate_type)
        return ctx.json_type_variable.is_null()


class IsNotNull(BaseNullPredicate):
    type_of: Literal['IsNotNull'] = 'IsNotNull'

    def __invert__(self):
        return IsNull()

    def to_z3(self, ctx: VariableContext):
        ctx.get_variable(self.predicate_type)
        return z3.Not(ctx.json_type_variable.is_null())
