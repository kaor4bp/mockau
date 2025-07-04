from abc import ABC, abstractmethod
from typing import Literal
from uuid import uuid4

import z3

from core.predicates.base_predicate import BaseCollectionPredicate, PredicateTypeVar
from core.predicates.collections.array_predicates import (
    ArrayContains,
    ArrayNotContains,
    ArrayNotStrictEqualTo,
    ArrayStrictEqualTo,
    BaseArrayPredicate,
)
from core.predicates.collections.object_predicates import (
    BaseObjectPredicate,
    ObjectContainsSubset,
    ObjectEqualTo,
    ObjectNotContainsSubset,
    ObjectNotEqualTo,
)
from core.predicates.consts import PredicateType
from core.predicates.context.variable_context import PredicateLimitations, VariableContext
from core.predicates.logical.logical_predicates import NotPredicate

_DEFAULT_NESTED_PREDICATES_EXTRA_NESTING = 2
EXTRA_NESTING = 1  # magic value to prevent some PredicateLimitations issues


class BaseNested(BaseCollectionPredicate, ABC):
    type_of: Literal['NestedArrayStrictEqualTo'] = 'NestedArrayStrictEqualTo'
    # max_depth: int = 10
    value: list | dict

    def is_intersected_with(self, other: PredicateTypeVar) -> bool:
        check_result = z3.unknown
        enable_quick_check = True

        limitation = self.calculate_limitations()
        limitation.push(other.calculate_limitations())
        for main_context, z3_solver in self._solver_iter(max_nesting_level=limitation.get_max_level()):
            ctx = VariableContext(main_context=main_context)
            ctx.main_context.set_limitations(limitation)

            z3_solver.add(self.to_z3(ctx))
            cur_constraints = ctx.pop_from_global_constraints()

            if enable_quick_check:
                for sub_predicate in other.get_nested_predicates():
                    z3_solver.push()
                    z3_solver.add(sub_predicate.to_z3(ctx))
                    z3_solver.add(ctx.pop_from_global_constraints())
                    z3_solver.add(cur_constraints)

                    check_result = z3_solver.check()
                    z3_solver.pop()

                    if check_result == z3.sat:
                        del ctx
                        return True
                else:
                    enable_quick_check = False

            z3_solver.add(other.to_z3(ctx))
            z3_solver.add(ctx.pop_from_global_constraints())
            z3_solver.add(cur_constraints)

            check_result = z3_solver.check()
            if check_result != z3.unknown:
                break

        del ctx
        assert check_result != z3.unknown
        return check_result == z3.sat

    # def is_superset_of(self, other: PredicateTypeVar) -> bool:
    #     if not self.is_intersected_with(other):
    #         return False
    #
    #     check_result = z3.unknown
    #     is_lol = False
    #
    #     for z3_solver in self._solver_iter():
    #         ctx = VariableContext()
    #
    #         limitation = (~self).calculate_limitations()
    #         limitation.push(other.calculate_limitations())
    #         ctx.set_limitations(limitation)
    #
    #         z3_solver.add(NotPredicate(predicate=self, preserve_type=False).to_z3(ctx))
    #         cur_constraints = ctx.pop_from_global_constraints()
    #
    #         if is_lol is False:
    #             for sub_predicate in other.get_sub_predicates():
    #                 z3_solver.push()
    #
    #                 z3_solver.add(sub_predicate.to_z3(ctx))
    #                 z3_solver.add(ctx.pop_from_global_constraints())
    #                 z3_solver.add(cur_constraints)
    #
    #                 check_result = z3_solver.check()
    #                 z3_solver.pop()
    #
    #                 if check_result == z3.sat:
    #                     del ctx
    #                     return False
    #             else:
    #                 is_lol = True
    #
    #         z3_solver.add(other.to_z3(ctx))
    #         z3_solver.add(ctx.pop_from_global_constraints())
    #         z3_solver.add(cur_constraints)
    #         check_result = z3_solver.check()
    #         if check_result != z3.unknown:
    #             break
    #
    #     del ctx
    #     assert check_result != z3.unknown
    #     return check_result in [z3.unsat, z3.unknown]

    @property
    @abstractmethod
    def sub_predicate(self):
        pass

    @abstractmethod
    def __invert__(self):
        pass

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array, PredicateType.Object}

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        main_predicate = self.sub_predicate(value=self.value)
        constraints = []
        initial_level = ctx.level

        for sub_level in range(ctx.main_context.limitations.get_max_level() + EXTRA_NESTING):
            child_ctx = ctx.create_child_context()

            object_iterator = z3.String(f'iter_obj_{uuid4()}', ctx=ctx.z3_context)
            array_iterator = z3.Int(f'iter_arr_{uuid4()}', ctx=ctx.z3_context)
            if (
                # sub_level < 10
                ctx.get_limitations().max_nesting_level + EXTRA_NESTING >= sub_level + initial_level
            ):
                array_var = ctx.get_variable(PredicateType.Array)
                object_var = ctx.get_variable(PredicateType.Object)
                constraints.append(
                    z3.Or(
                        main_predicate.to_z3(ctx),
                        z3.And(
                            array_var[array_iterator] == child_ctx.json_type_variable.z3_variable,
                            ctx.json_type_variable.is_array(),
                            array_iterator < z3.Length(array_var),
                            array_iterator >= z3.IntVal(0, ctx=ctx.z3_context),
                        ),
                        z3.And(
                            object_var[object_iterator] == child_ctx.json_type_variable.z3_variable,
                            ctx.json_type_variable.is_object(),
                        ),
                    )
                )
            else:
                constraints.append(main_predicate.to_z3(ctx))
            ctx = child_ctx

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


class BaseNestedNot(BaseNested, ABC):
    def build_nested_for_all(self, ctx, cur_obj, level, recursion_level=0, start_level=0):
        dts = ctx.main_context.AllJsonTypes

        object_iterator = z3.String(f'obj_iter_{uuid4()}', ctx=ctx.z3_context)
        array_iterator = z3.Int(f'arr_iter_{uuid4()}', ctx=ctx.z3_context)

        nested_object_expression = z3.BoolVal(True, ctx=ctx.z3_context)
        nested_array_expression = z3.BoolVal(True, ctx=ctx.z3_context)

        if (
            # recursion_level < 10
            level <= ctx.get_limitations().max_nesting_level + EXTRA_NESTING
            # and ctx.get_limitations().max_nesting_level >= level
        ):
            child_ctx = ctx.create_child_context()
            nested_object_expression = z3.ForAll(
                [object_iterator],
                self.build_nested_for_all(
                    ctx=child_ctx,
                    cur_obj=dts[level].get_object(cur_obj)[object_iterator],
                    level=level + 1,
                    recursion_level=recursion_level + 1,
                    start_level=start_level,
                ),
            )
            nested_array_expression = z3.ForAll(
                [array_iterator],
                z3.Implies(
                    z3.And(array_iterator >= 0, array_iterator < z3.Length(dts[level].get_array(cur_obj))),
                    self.build_nested_for_all(
                        ctx=child_ctx,
                        cur_obj=dts[level].get_array(cur_obj)[array_iterator],
                        level=level + 1,
                        recursion_level=recursion_level + 1,
                        start_level=start_level,
                    ),
                ),
            )

        if start_level <= level:
            sibling_ctx = ctx.create_sibling_context()
            main_predicate = self.sub_predicate(value=self.value)
            sub_predicate_expression = z3.And(
                main_predicate.to_z3(sibling_ctx),
                sibling_ctx.json_type_variable.z3_variable == cur_obj,
                sibling_ctx.pop_from_global_constraints(),
            )
            del sibling_ctx

            if main_predicate.predicate_types == {PredicateType.Array}:
                nested_array_expression = z3.And(nested_array_expression, sub_predicate_expression)
            else:
                nested_object_expression = z3.And(nested_object_expression, sub_predicate_expression)

        return z3.And(
            *[
                z3.Implies(
                    dts[level].is_object(cur_obj),
                    nested_object_expression,
                ),
                z3.Implies(
                    dts[level].is_array(cur_obj),
                    nested_array_expression,
                ),
            ]
        )

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        return self.build_nested_for_all(
            ctx=ctx,
            level=ctx.level,
            cur_obj=ctx.json_type_variable.z3_variable,
            start_level=ctx.level,
        )


class BaseNestedArray(BaseNested, BaseArrayPredicate, ABC):
    value: list

    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += item.get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations(
            level_gte=0,
            level_lte=None,
        )

        for item in self.value:
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))

        limitation.max_nesting_level += _DEFAULT_NESTED_PREDICATES_EXTRA_NESTING
        limitation.max_array_size = len(self.value) * 2 + 1
        return limitation

    def verify(self, value: dict | list):
        main_predicate = self.sub_predicate(value=self.value)

        if main_predicate.verify(value):
            return True

        if isinstance(value, dict):
            for item in value.values():
                if isinstance(item, list) and self.verify(item):
                    return True
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, list):
                    if main_predicate.verify(item):
                        return True
                    elif self.verify(item):
                        return True
                if isinstance(item, dict) and self.verify(item):
                    return True
        return False


class BaseNestedArrayNot(BaseNestedNot, BaseArrayPredicate, ABC):
    def get_nested_predicates(self):
        results = [self]
        for item in self.value:
            results += NotPredicate(predicate=item, preserve_type=False).get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations(
            level_gte=0,
            level_lte=None,
        )

        for item in self.value:
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))

        limitation.max_nesting_level += _DEFAULT_NESTED_PREDICATES_EXTRA_NESTING
        limitation.max_array_size = len(self.value) * 2 + 10
        return limitation

    def verify(self, value: list):
        main_predicate = self.sub_predicate(value=self.value)
        if main_predicate.verify(value):
            return True

        if not isinstance(value, list):
            return False

        for item in value:
            if isinstance(item, list):
                if not main_predicate.verify(item):
                    return False
                elif not self.verify(item):
                    return False
            if isinstance(item, dict):
                for value in item.values():
                    if isinstance(item, list) and not self.verify(value):
                        return False
        return True


class BaseNestedObject(BaseNested, BaseObjectPredicate, ABC):
    value: dict

    def get_nested_predicates(self):
        results = [self]
        for item in self.value.values():
            results += item.get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations(
            level_gte=0,
            level_lte=None,
        )

        for item in self.value.keys():
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))
        for item in self.value.values():
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))

        limitation.max_nesting_level += _DEFAULT_NESTED_PREDICATES_EXTRA_NESTING
        return limitation

    def verify(self, value: dict | list):
        main_predicate = self.sub_predicate(value=self.value)
        if main_predicate.verify(value):
            return True

        if isinstance(value, list):
            for item in value:
                if isinstance(item, dict) and self.verify(item):
                    return True
        elif isinstance(value, dict):
            for k, v in value.items():
                if isinstance(v, dict):
                    if self.sub_predicate(value=self.value).verify(v):
                        return True
                    elif self.verify(v):
                        return True
                if isinstance(v, list) and self.verify(v):
                    return True
        return False


class BaseNestedObjectNot(BaseNestedNot, BaseObjectPredicate, ABC):
    def get_nested_predicates(self):
        results = [self]
        for item in self.value.values():
            results += NotPredicate(predicate=item, preserve_type=False).get_nested_predicates()
        return results

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = PredicateLimitations(
            level_gte=0,
            level_lte=None,
        )

        for item in self.value.keys():
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))
        for item in self.value.values():
            limitation.push(item.calculate_limitations().increment_level(reset_level_lte=True))

        limitation.max_nesting_level += _DEFAULT_NESTED_PREDICATES_EXTRA_NESTING
        return limitation

    def verify(self, value: dict):
        main_predicate = self.sub_predicate(value=self.value)
        if main_predicate.verify(value):
            return True

        if not isinstance(value, dict):
            return False

        for k, v in value.items():
            if isinstance(v, dict):
                if not self.sub_predicate(value=self.value).verify(v):
                    return False
                elif not self.verify(v):
                    return False
            if isinstance(v, list):
                for item in v:
                    if isinstance(item, dict) and not self.verify(item):
                        return False
        return True


class NestedObjectEqualTo(BaseNestedObject):
    type_of: Literal['NestedObjectEqualTo'] = 'NestedObjectEqualTo'

    @property
    def sub_predicate(self):
        return ObjectEqualTo

    def __invert__(self):
        return NestedObjectNotEqualTo(value=self.value)


class NestedObjectNotEqualTo(BaseNestedObjectNot):
    type_of: Literal['NestedObjectNotEqualTo'] = 'NestedObjectNotEqualTo'

    @property
    def sub_predicate(self):
        return ObjectNotEqualTo

    def __invert__(self):
        return NestedObjectEqualTo(value=self.value)


class NestedObjectContainsSubset(BaseNestedObject):
    type_of: Literal['NestedObjectContainsSubset'] = 'NestedObjectContainsSubset'

    @property
    def sub_predicate(self):
        return ObjectContainsSubset

    def __invert__(self):
        return NesteObjectNotContainsSubset(value=self.value)


class NesteObjectNotContainsSubset(BaseNestedObjectNot):
    type_of: Literal['NestedObjectNotContainsSubset'] = 'NestedObjectNotContainsSubset'

    @property
    def sub_predicate(self):
        return ObjectNotContainsSubset

    def __invert__(self):
        return NestedObjectContainsSubset(value=self.value)


class NestedArrayStrictEqualTo(BaseNestedArray):
    type_of: Literal['NestedArrayStrictEqualTo'] = 'NestedArrayStrictEqualTo'

    @property
    def sub_predicate(self):
        return ArrayStrictEqualTo

    def __invert__(self):
        return NestedArrayNotStrictEqualTo(value=self.value)


class NestedArrayNotStrictEqualTo(BaseNestedArrayNot):
    type_of: Literal['NestedArrayNotStrictEqualTo'] = 'NestedArrayNotStrictEqualTo'

    @property
    def sub_predicate(self):
        return ArrayNotStrictEqualTo

    def __invert__(self):
        return NestedArrayStrictEqualTo(value=self.value)


class NestedArrayContains(BaseNestedArray):
    type_of: Literal['NestedArrayContains'] = 'NestedArrayContains'

    @property
    def sub_predicate(self):
        return ArrayContains

    def __invert__(self):
        return NestedArrayNotContains(value=self.value)


class NestedArrayNotContains(BaseNestedArrayNot):
    type_of: Literal['NestedArrayNotContains'] = 'NestedArrayNotContains'

    @property
    def sub_predicate(self):
        return ArrayNotContains

    def __invert__(self):
        return NestedArrayContains(value=self.value)
