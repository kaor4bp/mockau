from abc import ABC
from functools import cached_property
from typing import Generic, Literal, TypeVar
from uuid import uuid4

import z3

from core.predicates.base_predicate import BaseCollectionPredicate, PredicateType, VariableContext
from core.predicates.context.predicate_limitations import PredicateLimitations
from core.predicates.helpers import py_value_to_predicate
from utils.kuhn_matching_algorithm import KuhnMatchingAlgorithm

_t_SpecifiedType = TypeVar('_t_SpecifiedType')


class BaseGenericArrayPredicate(
    BaseCollectionPredicate,
    Generic[_t_SpecifiedType],
    ABC,
):
    value: list[_t_SpecifiedType]

    @cached_property
    def compiled_value(self):
        return [py_value_to_predicate(item) for item in self.value]

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations()

        for item in self.compiled_value:
            limitation.push(item.calculate_limitations().increment_level())

        limitation.max_array_size = len(self.compiled_value)
        return limitation


class BaseArrayItemPredicate(
    BaseCollectionPredicate,
    Generic[_t_SpecifiedType],
    ABC,
):
    predicate: _t_SpecifiedType

    def compile_predicate(self):
        return self._get_default_origin()(predicate=self.predicate.compile_predicate())

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array}

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations()

        limitation.push(self.predicate.calculate_limitations().increment_level())
        limitation.max_array_size = 3
        return limitation


class GenericArrayEqualTo(
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-array-equal-to'] = '$-mockau-array-equal-to'
    value: list[_t_SpecifiedType]
    ignore_order: bool = False

    def compile_predicate(self):
        from core.predicates import ArrayEqualTo

        return ArrayEqualTo(
            value=[item.compile_predicate() for item in self.compiled_value],
            ignore_order=self.ignore_order,
        )

    def _verify_without_order(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.compiled_value):
            return False

        graph = {}
        for item_predicate in self.compiled_value:
            graph[item_predicate] = []
            for item in value:
                if item_predicate.verify(item):
                    graph[item_predicate].append(item)

        best_combination = KuhnMatchingAlgorithm(graph).find_max_matching()
        return len(best_combination.keys()) == len(self.compiled_value)

    def _verify_with_order(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.compiled_value):
            return False
        for item_predicate, item in zip(self.compiled_value, value):
            if not item_predicate.verify(item):
                return False
        return True

    def verify(self, value: list):
        if self.ignore_order:
            return self._verify_without_order(value)
        else:
            return self._verify_with_order(value)

    def __invert__(self):
        from core.predicates import ArrayNotEqualTo

        return ArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += 1
        return limitation

    def _to_z3_with_order(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []

        for item_index, item in enumerate(self.compiled_value):
            child_ctx = ctx.create_child_context()

            constraints += [
                item.to_z3(child_ctx),
                array_var[item_index] == child_ctx.json_type_variable.z3_variable,
                child_ctx.pop_from_global_constraints(),
            ]

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.compiled_value), ctx=ctx.z3_context))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))

    def _to_z3_without_order(self, ctx: VariableContext) -> z3.ExprRef:
        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        all_index_vars = []

        for item in self.compiled_value:
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

        constraints.append(z3.Length(array_var) == z3.IntVal(len(self.compiled_value), ctx=ctx.z3_context))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        if self.ignore_order:
            return self._to_z3_without_order(ctx)
        else:
            return self._to_z3_with_order(ctx)


class GenericArrayNotEqualTo(
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-array-not-equal-to'] = '$-mockau-array-not-equal-to'
    value: list[_t_SpecifiedType]
    ignore_order: bool = False

    def compile_predicate(self):
        from core.predicates import ArrayNotEqualTo

        return ArrayNotEqualTo(
            value=[item.compile_predicate() for item in self.compiled_value],
            ignore_order=self.ignore_order,
        )

    def _verify_without_order(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.compiled_value):
            return True

        graph = {}
        for item_predicate in self.compiled_value:
            graph[item_predicate] = []
            for item in value:
                if item_predicate.verify(item):
                    graph[item_predicate].append(item)

        best_combination = KuhnMatchingAlgorithm(graph).find_max_matching()
        return len(best_combination.keys()) < len(self.compiled_value)

    def _verify_with_order(self, value: list):
        if not isinstance(value, list):
            return False

        if len(value) != len(self.compiled_value):
            return False
        for item_predicate, item in zip(self.compiled_value, value):
            if not item_predicate.verify(item):
                return True
        return False

    def verify(self, value: list):
        if self.ignore_order:
            return self._verify_without_order(value)
        else:
            return self._verify_with_order(value)

    def __invert__(self):
        from core.predicates import ArrayEqualTo

        return ArrayEqualTo(value=self.value, ignore_order=self.ignore_order)

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += len(self.compiled_value) + 1
        return limitation

    def _to_z3_with_order(self, ctx: VariableContext) -> z3.ExprRef:
        from core.predicates import NotPredicate

        array_var = ctx.get_variable(PredicateType.Array)
        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]

        for item_index, item in enumerate(self.compiled_value):
            child_ctx = ctx.create_child_context()
            constraints += [
                NotPredicate(predicate=item).to_z3(child_ctx),
                child_ctx.pop_from_global_constraints(),
            ]
            or_constraints.append(array_var[item_index] == child_ctx.json_type_variable.z3_variable)

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.compiled_value), ctx=ctx.z3_context))
        constraints.append(ctx.json_type_variable.is_array())

        return z3.And(*constraints, z3.Or(*or_constraints))

    def _to_z3_without_order(self, ctx: VariableContext) -> z3.ExprRef:
        from core.predicates import NotPredicate

        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]
        array_var = ctx.get_variable(PredicateType.Array)

        for item in self.compiled_value:
            child_ctx = ctx.create_child_context()
            expected_array = z3.Empty(z3.SeqSort(child_ctx.JsonType))

            for _ in range(ctx.get_limitations().max_array_size):
                child_ctx = ctx.create_child_context()

                constraints += [
                    NotPredicate(predicate=item).to_z3(child_ctx),
                    child_ctx.pop_from_global_constraints(),
                ]

                expected_array = z3.Concat(expected_array, z3.Unit(child_ctx.json_type_variable.z3_variable))

            or_constraints.append(array_var == z3.SubSeq(expected_array, 0, z3.Length(array_var)))

        or_constraints.append(z3.Length(array_var) != z3.IntVal(len(self.compiled_value), ctx=ctx.z3_context))

        constraints += [
            ctx.json_type_variable.is_array(),
            ctx.get_limitations().max_array_size >= z3.Length(array_var),
        ]

        return z3.And(*constraints, z3.Or(*or_constraints))

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        if self.ignore_order:
            return self._to_z3_without_order(ctx)
        else:
            return self._to_z3_with_order(ctx)


class GenericArrayContains(
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-array-contains'] = '$-mockau-array-contains'
    value: list[_t_SpecifiedType]

    def compile_predicate(self):
        from core.predicates import ArrayContains

        return ArrayContains(
            value=[item.compile_predicate() for item in self.compiled_value],
        )

    def verify(self, value: list):
        if not isinstance(value, list):
            return False

        for item_predicate in self.compiled_value:
            for item in value:
                if item_predicate.verify(item):
                    break
            else:
                return False
        return True

    def __invert__(self):
        from core.predicates import ArrayNotContains

        return ArrayNotContains(value=self.value)

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += len(self.compiled_value) + 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        array_var = ctx.get_variable(PredicateType.Array)
        all_index_vars = []

        for item in self.compiled_value:
            index_var = z3.Int(f'index_{uuid4()}', ctx=ctx.z3_context)

            for item_index in reversed(all_index_vars):
                constraints.append(index_var != item_index)
            all_index_vars.append(index_var)

            child_ctx = ctx.create_child_context()
            constraints += [
                item.to_z3(child_ctx),
                z3.Contains(array_var, z3.Unit(child_ctx.json_type_variable.z3_variable)),
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


class GenericArrayNotContains(
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-array-not-contains'] = '$-mockau-array-not-contains'
    value: list[_t_SpecifiedType]

    def compile_predicate(self):
        from core.predicates import ArrayNotContains

        return ArrayNotContains(
            value=[item.compile_predicate() for item in self.compiled_value],
        )

    def verify(self, value: list):
        return not GenericArrayContains(value=self.value).verify(value)

    def __invert__(self):
        from core.predicates import ArrayContains

        return ArrayContains(value=self.value)

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = super().calculate_limitations()
        limitation.max_array_size += 1
        return limitation

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        from core.predicates import NotPredicate

        constraints = []
        or_constraints = [z3.BoolVal(False, ctx=ctx.z3_context)]
        array_var = ctx.get_variable(PredicateType.Array)

        for item in self.compiled_value:
            inverted_item = NotPredicate(predicate=item)
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
