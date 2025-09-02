from abc import ABC
from typing import TYPE_CHECKING, Literal
from uuid import uuid4

import z3

from core.predicates.base_predicate import BaseCollectionPredicate, ParityPredicateMixin
from core.predicates.consts import ALLOWED_POOL_PREDICATE_TYPES, PredicateType
from core.predicates.context.predicate_limitations import PredicateLimitations
from core.predicates.context.variable_context import VariableContext
from core.predicates.helpers import py_value_to_predicate

if TYPE_CHECKING:
    from core.predicates import t_DefaultPredicateType


class NestedAnyOf(BaseCollectionPredicate, ABC):
    type_of: Literal['$-minow-nested-any-of'] = '$-minow-nested-any-of'

    predicate: 't_DefaultPredicateType'

    def get_all_predicates(self):
        yield self.compiled_value
        yield from self.compiled_value.get_all_predicates()

    @property
    def compiled_value(self):
        return py_value_to_predicate(self.predicate)

    def verify(self, value: dict | list):
        if self.compiled_value.verify(value):
            return True

        if isinstance(value, dict):
            for item in value.values():
                if self.verify(item):
                    return True
        elif isinstance(value, list):
            for item in value:
                if self.verify(item):
                    return True
        return False

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = self.compiled_value.calculate_limitations().reset_level_lte()
        limitation.add_level()
        # limitation.max_array_size = 10
        return limitation

    def __invert__(self):
        return NestedAllOf(predicate=~self.predicate, var=self.var)

    @property
    def predicate_types(self) -> set[PredicateType]:
        predicate_types = {PredicateType.Array, PredicateType.Object}
        return predicate_types.union(self.compiled_value.predicate_types)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        ctx.set_as_user_variable(self.var)
        constraints = []

        max_sub_level = (
            ctx.main_context.limitations.get_max_level()
            - self.compiled_value.calculate_limitations().get_max_level()
            - ctx.level
        )

        for sub_level in range(max_sub_level):
            child_ctx = ctx.create_child_context()

            object_iterator = z3.String(f'iter_obj_{uuid4()}', ctx=ctx.z3_context)
            array_iterator = z3.Int(f'iter_arr_{uuid4()}', ctx=ctx.z3_context)
            array_var = ctx.get_variable(PredicateType.Array)
            object_var = ctx.get_variable(PredicateType.Object)

            sibling_ctx = ctx.create_sibling_context()
            expression = z3.And(
                self.compiled_value.to_z3(sibling_ctx),
                sibling_ctx.json_type_variable.z3_variable == ctx.json_type_variable.z3_variable,
                sibling_ctx.pop_from_global_constraints(),
            )

            constraints.append(
                z3.Or(
                    expression,
                    z3.And(
                        array_var[array_iterator] == child_ctx.json_type_variable.z3_variable,
                        ctx.json_type_variable.is_array(),
                        array_iterator < z3.Length(array_var),
                        array_iterator >= z3.IntVal(0, ctx=ctx.z3_context),
                        z3.Length(array_var) <= z3.IntVal(ctx.get_limitations().max_array_size, ctx=ctx.z3_context),
                    ),
                    z3.And(
                        object_var[object_iterator] == child_ctx.json_type_variable.z3_variable,
                        # z3.Contains(ctx.main_context.get_all_object_keys_var(), z3.Unit(object_iterator)),
                        ctx.json_type_variable.is_object(),
                    ),
                )
            )
            ctx = child_ctx

        constraints.append(self.compiled_value.to_z3(ctx))

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


class NestedAllOf(NestedAnyOf, ParityPredicateMixin, ABC):
    type_of: Literal['$-minow-nested-all-of'] = '$-minow-nested-all-of'

    def __invert__(self):
        return NestedAnyOf(predicate=~self.predicate, var=self.var)

    @property
    def predicate_types(self) -> set[PredicateType]:
        if self._parity:
            predicate_types = {PredicateType.Array, PredicateType.Object}
            return predicate_types.union(self.compiled_value.predicate_types)
        else:
            return ALLOWED_POOL_PREDICATE_TYPES

    def verify(self, value):
        return self.is_intersected_with(py_value_to_predicate(value))
        # if self.compiled_value.verify(value):
        #     return True
        #
        # if isinstance(value, list):
        #     for item in value:
        #         if not self.compiled_value.verify(item):
        #             return False
        # if isinstance(value, dict):
        #     for value in value.values():
        #         if not self.verify(value):
        #             return False
        #
        # return True

    def build_nested_for_all(self, ctx, cur_obj, level, start_level=0):
        dts = ctx.main_context.AllJsonTypes

        object_iterator = z3.String(f'obj_iter_{uuid4()}', ctx=ctx.z3_context)
        array_iterator = z3.Int(f'arr_iter_{uuid4()}', ctx=ctx.z3_context)

        max_allowed_level = (
            ctx.main_context.limitations.get_max_level() - self.compiled_value.calculate_limitations().get_max_level()
        )

        nested_object_expression = z3.BoolVal(True, ctx=ctx.z3_context)
        nested_array_expression = z3.BoolVal(True, ctx=ctx.z3_context)

        if level < max_allowed_level:
            child_ctx = ctx.create_child_context()
            nested_object_expression = z3.And(
                z3.ForAll(
                    [object_iterator],
                    z3.And(
                        # z3.Contains(ctx.main_context.get_all_object_keys_var(), z3.Unit(object_iterator)),
                        self.build_nested_for_all(
                            ctx=child_ctx,
                            cur_obj=dts[level].get_object(cur_obj)[object_iterator],
                            level=level + 1,
                            start_level=start_level,
                        )
                    ),
                )
            )
            nested_array_expression = z3.ForAll(
                [array_iterator],
                z3.Implies(
                    z3.And(
                        array_iterator >= 0,
                        array_iterator < z3.Length(dts[level].get_array(cur_obj)),
                    ),
                    self.build_nested_for_all(
                        ctx=child_ctx,
                        cur_obj=dts[level].get_array(cur_obj)[array_iterator],
                        level=level + 1,
                        start_level=start_level,
                    ),
                ),
            )
            nested_array_expression = z3.And(
                z3.Length(dts[level].get_array(cur_obj))
                <= z3.IntVal(ctx.get_limitations().max_array_size, ctx=ctx.z3_context),
                nested_array_expression,
            )

        nested_expressions = {pt: z3.BoolVal(True, ctx=ctx.z3_context) for pt in PredicateType}

        if level >= start_level:
            sibling_ctx = ctx.create_sibling_context()
            sub_predicate_expression = z3.And(
                self.compiled_value.to_z3(sibling_ctx),
                sibling_ctx.json_type_variable.z3_variable == cur_obj,
                sibling_ctx.pop_from_global_constraints(),
            )
            del sibling_ctx

            for pt in PredicateType:
                if (
                    pt in self.compiled_value.predicate_types
                    or PredicateType.Any in self.compiled_value.predicate_types
                ):
                    nested_expressions[pt] = sub_predicate_expression

        return z3.And(
            *[
                z3.Implies(
                    dts[level].is_object(cur_obj),
                    z3.And(
                        nested_object_expression,
                        nested_expressions[PredicateType.Object],
                    ),
                ),
                z3.Implies(
                    dts[level].is_array(cur_obj),
                    z3.And(
                        nested_array_expression,
                        nested_expressions[PredicateType.Array],
                    ),
                ),
                z3.Implies(
                    dts[level].is_str(cur_obj),
                    nested_expressions[PredicateType.String],
                ),
                z3.Implies(
                    dts[level].is_int(cur_obj),
                    nested_expressions[PredicateType.Integer],
                ),
                z3.Implies(
                    dts[level].is_real(cur_obj),
                    nested_expressions[PredicateType.Real],
                ),
                z3.Implies(
                    dts[level].is_bool(cur_obj),
                    nested_expressions[PredicateType.Boolean],
                ),
                z3.Implies(
                    dts[level].is_null(cur_obj),
                    nested_expressions[PredicateType.Null],
                ),
                z3.Implies(
                    dts[level].is_undefined(cur_obj),
                    nested_expressions[PredicateType.Undefined],
                ),
            ]
        )

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        ctx.set_as_user_variable(self.var)
        return self.build_nested_for_all(
            ctx=ctx,
            level=ctx.level,
            cur_obj=ctx.json_type_variable.z3_variable,
            start_level=ctx.level,
        )


class NestedNoneOf(NestedAllOf):
    type_of: Literal['$-minow-nested-none-of'] = '$-minow-nested-none-of'

    @property
    def compiled_value(self):
        return ~py_value_to_predicate(self.predicate)
