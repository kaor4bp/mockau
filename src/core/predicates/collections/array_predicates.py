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
from utils.kuhn_matching_algorithm import KuhnMatchingAlgorithm


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

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.value):
            return False
        for item_predicate, item in zip(self.value, value):
            if not item_predicate.verify(item):
                return False
        return True

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

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.value):
            return False
        for item_predicate, item in zip(self.value, value):
            if not item_predicate.verify(item):
                return True
        return False

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

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.value):
            return False

        graph = {}
        for item_predicate in self.value:
            graph[item_predicate] = []
            for item in value:
                if item_predicate.verify(item):
                    graph[item_predicate].append(item)

        best_combination = KuhnMatchingAlgorithm(graph).find_max_matching()
        return len(best_combination.keys()) == len(self.value)

    def __invert__(self):
        return ArrayNotEqualToWithoutOrder(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        all_index_vars = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}')

            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            constraints.append(
                array_var[index_var] == child_ctx.json_type_variable.z3_variable,
            )
            constraints.append(index_var >= z3.IntVal(0))
            constraints.append(index_var < z3.Length(array_var))
            for v in all_index_vars:
                constraints.append(index_var != v)
            all_index_vars.append(index_var)

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.value)))
        constraints.append(ctx.json_type_variable.is_array())

        ctx.set_array_len(len(self.value))

        return z3.And(*constraints)


class ArrayNotEqualToWithoutOrder(BaseArrayPredicate):
    type_of: Literal['ArrayEqualToWithoutOrder'] = 'ArrayEqualToWithoutOrder'

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.value):
            return True

        graph = {}
        for item_predicate in self.value:
            graph[item_predicate] = []
            for item in value:
                if item_predicate.verify(item):
                    graph[item_predicate].append(item)

        best_combination = KuhnMatchingAlgorithm(graph).find_max_matching()
        return len(best_combination.keys()) < len(self.value)

    def __invert__(self):
        return ArrayEqualToWithoutOrder(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        all_index_vars = []
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
            for v in all_index_vars:
                constraints.append(index_var != v)
            all_index_vars.append(index_var)

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.value)))

        ctx.set_array_len(len(self.value))
        ctx.add_unbounded_array(array_var)

        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.Or(*or_constraints))


class ArrayContains(BaseArrayPredicate):
    type_of: Literal['ArrayContains'] = 'ArrayContains'

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        for item_predicate in self.value:
            for item in value:
                if item_predicate.verify(item):
                    break
            else:
                return False
        return True

    def __invert__(self):
        return ArrayNotContains(value=self.value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        array_var = ctx.get_variable(PredicateType.Array)
        all_index_vars = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}')

            for v in all_index_vars:
                constraints.append(index_var != v)
            all_index_vars.append(index_var)

            child_ctx = ctx.create_child_context()
            constraints.append(item.to_z3(child_ctx))
            constraints.append(child_ctx.json_type_variable.z3_variable == array_var[index_var])
            constraints.append(index_var >= z3.IntVal(0))
            constraints.append(index_var < z3.Length(array_var))

        ctx.set_array_len(len(self.value) * 2)
        ctx.add_unbounded_array(array_var)

        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints)


class ArrayNotContains(BaseArrayPredicate):
    type_of: Literal['ArrayNotContains'] = 'ArrayNotContains'

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        for item_predicate in self.value:
            for item in value:
                if not item_predicate.verify(item):
                    return True

        return False

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
