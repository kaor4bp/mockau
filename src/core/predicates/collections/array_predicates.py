from abc import ABC
from typing import Literal, Self
from uuid import uuid4

import z3
from pydantic import model_validator

from core.predicates.base_predicate import (
    BaseCollectionPredicate,
    BasePredicate,
    PredicateType,
    VariableContext,
    t_Predicate,
)
from core.predicates.helpers import value_to_predicate


class BaseArrayPredicate(BaseCollectionPredicate, ABC):
    value: list

    @model_validator(mode='after')
    def handle_nested_objects(self) -> Self:
        for item_index, item in enumerate(self.value):
            if not isinstance(item, BasePredicate):
                self.value[item_index] = value_to_predicate(item)
        return self

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}


class BaseArrayItemPredicate(BaseCollectionPredicate):
    predicate: t_Predicate | str | int | bool | None

    @model_validator(mode='after')
    def handle_nested_objects(self) -> Self:
        if not isinstance(self.predicate, BasePredicate):
            self.predicate = value_to_predicate(self.predicate)
        return self

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}


class ArrayStrictEqualTo(BaseArrayPredicate):
    type_of: Literal['ArrayStrictEqualTo'] = 'ArrayStrictEqualTo'

    def __invert__(self):
        return ArrayNotStrictEqualTo(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        child_ctx = ctx.create_child_context()
        array_values = z3.EmptySet(child_ctx.json_type_variable.JsonType)

        for item_index, item in enumerate(self.value):
            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            constraints.append(array_var[item_index] == child_ctx.json_type_variable.z3_variable)
            array_values = z3.SetAdd(array_values, child_ctx.json_type_variable.z3_variable)

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.value)))
        constraints.append(ctx.json_type_variable.is_array())

        ctx.set_array_len(len(self.value))

        return z3.And(*constraints)


class ArrayNotStrictEqualTo(BaseArrayPredicate):
    type_of: Literal['ArrayStrictEqualTo'] = 'ArrayStrictEqualTo'

    def __invert__(self):
        return ArrayStrictEqualTo(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        child_ctx = ctx.create_child_context()
        array_values = z3.EmptySet(child_ctx.json_type_variable.JsonType)
        or_constraints = []

        for item_index, item in enumerate(self.value):
            child_ctx = ctx.create_child_context()
            constraints.append((~item).to_z3(child_ctx))
            or_constraints.append(array_var[item_index] == child_ctx.json_type_variable.z3_variable)
            array_values = z3.SetAdd(array_values, child_ctx.json_type_variable.z3_variable)

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.value)))

        ctx.set_array_len(len(self.value))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.Or(*or_constraints))


class ArrayEqualToWithoutOrder(BaseArrayPredicate):
    type_of: Literal['ArrayEqualToWithoutOrder'] = 'ArrayEqualToWithoutOrder'

    def __invert__(self):
        return ArrayNotEqualToWithoutOrder(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        value_indexes = z3.Const(f'all_indexes_{uuid4()}', z3.SeqSort(z3.IntSort()))
        constraints = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}')

            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            constraints.append(
                array_var[index_var] == child_ctx.json_type_variable.z3_variable,
            )
            constraints.append(index_var >= z3.IntVal(0))
            constraints.append(index_var < z3.Length(array_var))
            value_indexes = z3.Concat(value_indexes, z3.Unit(index_var))

        constraints.append(z3.Distinct(value_indexes))
        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.value)))
        constraints.append(ctx.json_type_variable.is_array())

        ctx.set_array_len(len(self.value))

        return z3.And(*constraints)


class ArrayNotEqualToWithoutOrder(BaseArrayPredicate):
    type_of: Literal['ArrayEqualToWithoutOrder'] = 'ArrayEqualToWithoutOrder'

    def __invert__(self):
        return ArrayEqualToWithoutOrder(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        value_indexes = z3.Const(f'all_indexes_{uuid4()}', z3.SeqSort(z3.IntSort()))
        constraints = []
        or_constraints = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}')

            child_ctx = ctx.create_child_context()

            constraints.append(item.to_z3(child_ctx))

            or_constraints += [
                # array_var[index_var] != child_ctx.json_type_variable.z3_variable,
                z3.Not(z3.Contains(array_var, z3.Unit(child_ctx.json_type_variable.z3_variable)))
            ]
            constraints.append(index_var >= z3.IntVal(0))
            constraints.append(index_var < z3.Length(array_var))
            value_indexes = z3.Concat(value_indexes, z3.Unit(index_var))

        constraints.append(z3.Distinct(value_indexes))
        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.value)))

        ctx.set_array_len(len(self.value))
        ctx.add_unbounded_array(array_var)

        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.Or(*or_constraints))


class ArrayContains(BaseArrayPredicate):
    type_of: Literal['ArrayContains'] = 'ArrayContains'

    def __invert__(self):
        return ArrayNotContains(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        array_var = ctx.get_variable(PredicateType.Array)
        indexes_seq = z3.Const(f'indexes_{uuid4()}', z3.SeqSort(z3.IntSort()))

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}')

            indexes_seq = z3.Concat(indexes_seq, z3.Unit(index_var))

            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            constraints.append(child_ctx.json_type_variable.z3_variable == array_var[index_var])
            constraints.append(index_var >= z3.IntVal(0))
            constraints.append(index_var < z3.Length(array_var))

        ctx.set_array_len(len(self.value) * 2)
        ctx.add_unbounded_array(array_var)

        constraints.append(z3.Distinct(indexes_seq))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints)


class ArrayNotContains(BaseArrayPredicate):
    type_of: Literal['ArrayNotContains'] = 'ArrayNotContains'

    def __invert__(self):
        return ArrayContains(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        or_constraints = []
        array_var = ctx.get_variable(PredicateType.Array)

        for item in self.value:
            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            or_constraints.append(z3.Not(z3.Contains(array_var, z3.Unit(child_ctx.json_type_variable.z3_variable))))

        ctx.set_array_len(len(self.value) * 2)
        ctx.add_unbounded_array(array_var)

        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.Or(*or_constraints))
