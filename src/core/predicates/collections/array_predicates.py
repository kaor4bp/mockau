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
from core.predicates.context.variable_context import PredicateLimitations
from core.predicates.helpers import value_to_predicate
from core.predicates.logical.logical_predicates import NotPredicate
from utils.kuhn_matching_algorithm import KuhnMatchingAlgorithm

_DEFAULT_NESTED_PREDICATES_EXTRA_NESTING = 2


class BaseArrayPredicate(BaseCollectionPredicate, ABC):
    value: list

    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += item.get_nested_predicates()
        return results

    @model_validator(mode='after')
    def handle_nested_objects(self) -> Self:
        for item_index, item in enumerate(self.value):
            if not isinstance(item, BasePredicate):
                self.value[item_index] = value_to_predicate(item)
        return self

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations()

        for item in self.value:
            limitation.push(item.calculate_limitations().increment_level())

        limitation.max_nesting_level += 1
        limitation.max_array_size = len(self.value)
        return limitation


class BaseArrayItemPredicate(BaseCollectionPredicate):
    predicate: t_Predicate | str | int | bool | None

    def get_nested_predicates(self):
        return [self] + self.predicate.get_nested_predicates()

    @model_validator(mode='after')
    def handle_nested_objects(self) -> Self:
        if not isinstance(self.predicate, BasePredicate):
            self.predicate = value_to_predicate(self.predicate)
        return self

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations()

        limitation.push(self.predicate.calculate_limitations().increment_level())
        limitation.max_nesting_level += 1
        limitation.max_array_size = 3
        return limitation


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

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []

        for item_index, item in enumerate(self.value):
            child_ctx = ctx.create_child_context()

            constraints += [
                item.to_z3(child_ctx),
                array_var[item_index] == child_ctx.json_type_variable.z3_variable,
                child_ctx.pop_from_global_constraints(),
            ]

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.value), ctx=ctx.z3_context))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


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

    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += NotPredicate(predicate=item, preserve_type=False).get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += len(self.value) + 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]

        for item_index, item in enumerate(self.value):
            child_ctx = ctx.create_child_context()
            constraints += [
                NotPredicate(predicate=item, preserve_type=False).to_z3(child_ctx),
                child_ctx.pop_from_global_constraints(),
            ]
            or_constraints.append(array_var[item_index] == child_ctx.json_type_variable.z3_variable)

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.value), ctx=ctx.z3_context))
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

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        all_index_vars = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}', ctx=ctx.z3_context)

            child_ctx = ctx.create_child_context()
            constraints += [
                item.to_z3(child_ctx),
                array_var[index_var] == child_ctx.json_type_variable.z3_variable,
                child_ctx.pop_from_global_constraints(),
            ]

            constraints.append(index_var >= z3.IntVal(0, ctx=ctx.z3_context))
            constraints.append(index_var < z3.Length(array_var))

            for item_index in reversed(all_index_vars):
                constraints.append(index_var != item_index)
                break
            all_index_vars.append(index_var)

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.value), ctx=ctx.z3_context))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


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

    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += NotPredicate(predicate=item, preserve_type=False).get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += len(self.value) + 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]
        array_var = ctx.get_variable(PredicateType.Array)

        for item in self.value:
            child_ctx = ctx.create_child_context()
            expected_array = z3.Empty(z3.SeqSort(child_ctx.JsonType))

            for _ in range(ctx.get_limitations().max_array_size):
                child_ctx = ctx.create_child_context()

                constraints += [
                    NotPredicate(predicate=item, preserve_type=False).to_z3(child_ctx),
                    child_ctx.pop_from_global_constraints(),
                ]

                expected_array = z3.Concat(expected_array, z3.Unit(child_ctx.json_type_variable.z3_variable))

            or_constraints.append(array_var == z3.SubSeq(expected_array, 0, z3.Length(array_var)))

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.value), ctx=ctx.z3_context))

        constraints += [
            ctx.json_type_variable.is_array(),
            ctx.get_limitations().max_array_size >= z3.Length(array_var),
        ]

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

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += len(self.value) + 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        array_var = ctx.get_variable(PredicateType.Array)
        all_index_vars = []

        for item in self.value:
            index_var = z3.Int(f'index_{uuid4()}', ctx=ctx.z3_context)

            for item_index in reversed(all_index_vars):
                constraints.append(index_var != item_index)
            all_index_vars.append(index_var)

            child_ctx = ctx.create_child_context()
            constraints += [
                item.to_z3(child_ctx),
                # z3.Contains(array_var, z3.Unit(child_ctx.json_type_variable.z3_variable)),
                child_ctx.json_type_variable.z3_variable == array_var[index_var],
                index_var >= z3.IntVal(0, ctx=ctx.z3_context),
                index_var < z3.Length(array_var),
                child_ctx.pop_from_global_constraints(),
            ]

        constraints += [
            ctx.json_type_variable.is_array(),
            z3.IntVal(ctx.get_limitations().max_array_size, ctx=ctx.z3_context) >= z3.Length(array_var),
        ]

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


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

    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += NotPredicate(predicate=item, preserve_type=False).get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]
        array_var = ctx.get_variable(PredicateType.Array)

        for item in self.value:
            inverted_item = NotPredicate(predicate=item, preserve_type=False)
            child_ctx = ctx.create_child_context()
            expected_array = z3.Empty(z3.SeqSort(child_ctx.JsonType))

            for _ in range(ctx.get_limitations().max_array_size):
                child_ctx = ctx.create_child_context()

                constraints += [
                    inverted_item.to_z3(child_ctx),
                    child_ctx.pop_from_global_constraints(),
                ]

                expected_array = z3.Concat(expected_array, z3.Unit(child_ctx.json_type_variable.z3_variable))
                del child_ctx

            or_constraints.append(array_var == z3.SubSeq(expected_array, 0, z3.Length(array_var)))

        constraints += [
            ctx.json_type_variable.is_array(),
            ctx.get_limitations().max_array_size >= z3.Length(array_var),
        ]

        return z3.And(*constraints, z3.Or(*or_constraints))
