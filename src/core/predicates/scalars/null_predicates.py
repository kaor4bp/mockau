from typing import Literal

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext
from core.predicates.logical.logical_predicates import VoidPredicate


class BaseNullPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Null}


class IsNull(BaseNullPredicate):
    type_of: Literal['IsNull'] = 'IsNull'

    def verify(self, value):
        return value is None

    def __invert__(self):
        # `Not(IsNull)` usually means "non-null values."
        # But with `preserve_type=True`, we'd need a null-like type that isn't null — a logical impossibility
        return VoidPredicate()

    def to_z3(self, ctx: VariableContext):
        ctx.get_variable(self.predicate_type)
        return ctx.json_type_variable.is_null()
