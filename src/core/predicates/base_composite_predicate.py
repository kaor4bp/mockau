from copy import deepcopy

import z3
from pydantic import RootModel, model_validator

from core.predicates.base_predicate import BasePredicate
from core.predicates.consts import PredicateType
from core.predicates.context.variable_context import VariableContext
from core.predicates.helpers import deserialize_json_predicate_format, py_value_to_predicate


class BaseCompositePredicate(BasePredicate):
    @model_validator(mode='before')
    def handle_py2predicate(cls, data):
        if not isinstance(data, dict):
            return data

        data = deepcopy(data)
        for key, value in data.items():
            value = deserialize_json_predicate_format(value)
            data[key] = py_value_to_predicate(value)

        return data

    @model_validator(mode='after')
    def validate_predicates(self):
        for key in self.model_fields_set:
            value = getattr(self, key)
            if not isinstance(value, BasePredicate):
                raise ValueError(f'Value predicate must be a BasePredicate, got {value}')
        return self

    def compile_predicate(self):
        from core.predicates import ObjectContainsSubset

        result = {}

        for field_name in self.model_fields_set:
            field_value = getattr(self, field_name)
            if isinstance(field_value, RootModel):
                field_value = field_value.root.compile_predicate()
            result[field_name] = field_value.compile_predicate()

        return ObjectContainsSubset(value=result)

    def __invert__(self):
        return ~self.compile_predicate()

    def verify(self, value):
        return self.compile_predicate().verify(value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        return self.compile_predicate().to_z3(ctx)

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Object}

    # def is_subset_of(self: Self, other: Self) -> bool:
    #     assert isinstance(other, self.__class__)
    #     return self.compile_predicate().is_subset_of(other.compile_predicate())
    #
    # def is_superset_of(self: Self, other: Self) -> bool:
    #     assert isinstance(other, self.__class__)
    #     return self.compile_predicate().is_superset_of(other.compile_predicate())
    #
    # def is_intersected_with(self: Self, other: Self) -> bool:
    #     assert isinstance(other, self.__class__)
    #     return self.compile_predicate().is_intersected_with(other.compile_predicate())
    #
    # def is_equivalent_to(self: Self, other: Self) -> bool:
    #     assert isinstance(other, self.__class__)
    #     return self.compile_predicate().is_equivalent_to(other.compile_predicate())
