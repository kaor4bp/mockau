from typing import TYPE_CHECKING, Literal, Union

import z3
from pydantic import field_validator

from core.predicates.base_predicate import BasePredicate, BaseScalarPredicate, PredicateType, VariableContext
from core.predicates.helpers import py_value_to_predicate
from core.predicates.logical.logical_predicates import VoidPredicate

if TYPE_CHECKING:
    from core.predicates import t_Predicate, t_Py2PredicateType


class BaseNullPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.Null}


class IsNull(BaseNullPredicate):
    type_of: Literal['$-mockau-is-null'] = '$-mockau-is-null'

    def verify(self, value):
        return value is None

    def __invert__(self):
        # `Not(IsNull)` usually means "non-null values."
        # But with `preserve_type=True`, we'd need a null-like type that isn't null — a logical impossibility
        return VoidPredicate()

    def to_z3(self, ctx: VariableContext):
        ctx.get_variable(self.predicate_type)
        return ctx.json_type_variable.is_null()


class OptionalPredicate(BaseNullPredicate):
    type_of: Literal['$-mockau-optional'] = '$-mockau-optional'

    predicate: Union['t_Predicate', 't_Py2PredicateType']

    def normalize(self):
        from core.predicates import OrPredicate

        return OrPredicate(
            predicates=[IsNull(), self.predicate.normalize()],
        ).normalize()

    @field_validator('predicate', mode='before')
    @classmethod
    def handle_py2predicate(cls, data):
        return py_value_to_predicate(data)

    @field_validator('predicate', mode='after')
    @classmethod
    def validate_predicates(cls, value):
        if not isinstance(value, BasePredicate):
            raise ValueError(f'Item predicate must be a BasePredicate, got {value}')
        return value

    def verify(self, value):
        return value is None or self.predicate.verify(value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        return z3.Or(ctx.json_type_variable.is_null(), self.predicate.to_z3(ctx))
