from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Generic, Literal, TypeVar, Union
from uuid import uuid4

import z3

from core.predicates.base_predicate import BaseCollectionPredicate
from core.predicates.collections.array_predicates import BaseGenericArrayPredicate
from core.predicates.collections.object_predicates import BaseGenericObjectPredicate
from core.predicates.consts import PredicateType
from core.predicates.context.predicate_limitations import PredicateLimitations
from core.predicates.context.variable_context import VariableContext

if TYPE_CHECKING:
    from core.predicates import t_Predicate

_t_SpecifiedType = TypeVar('_t_SpecifiedType')


class BaseNested(BaseCollectionPredicate, ABC):
    value: list | dict

    @property
    @abstractmethod
    def sub_predicate(self):
        pass

    @property
    def sub_predicate_kwargs(self):
        return dict()

    @abstractmethod
    def __invert__(self):
        pass

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Array, PredicateType.Object}

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)
        constraints = []

        max_sub_level = (
            ctx.main_context.limitations.get_max_level()
            - main_predicate.calculate_limitations().get_max_level()
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
                main_predicate.to_z3(sibling_ctx),
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
                        ctx.json_type_variable.is_object(),
                    ),
                )
            )
            ctx = child_ctx

        constraints.append(main_predicate.to_z3(ctx))

        return z3.And(*constraints, z3.BoolVal(True, ctx=ctx.z3_context))


class BaseNestedNot(BaseNested, ABC):
    def build_nested_for_all(self, ctx, cur_obj, level, start_level=0):
        dts = ctx.main_context.AllJsonTypes
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)

        object_iterator = z3.String(f'obj_iter_{uuid4()}', ctx=ctx.z3_context)
        array_iterator = z3.Int(f'arr_iter_{uuid4()}', ctx=ctx.z3_context)

        nested_object_expression = z3.BoolVal(True, ctx=ctx.z3_context)
        nested_array_expression = z3.BoolVal(True, ctx=ctx.z3_context)

        max_allowed_level = (
            ctx.main_context.limitations.get_max_level() - main_predicate.calculate_limitations().get_max_level()
        )

        if level < max_allowed_level:
            child_ctx = ctx.create_child_context()
            nested_object_expression = z3.ForAll(
                [object_iterator],
                self.build_nested_for_all(
                    ctx=child_ctx,
                    cur_obj=dts[level].get_object(cur_obj)[object_iterator],
                    level=level + 1,
                    start_level=start_level,
                ),
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

        if level >= start_level:
            sibling_ctx = ctx.create_sibling_context()
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
                z3.BoolVal(True, ctx=ctx.z3_context),
            ]
        )

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        return self.build_nested_for_all(
            ctx=ctx,
            level=ctx.level,
            cur_obj=ctx.json_type_variable.z3_variable,
            start_level=ctx.level,
        )


class BaseNestedGenericArray(
    BaseNested,
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
    ABC,
):
    value: list[_t_SpecifiedType]

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = (
            self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).calculate_limitations().reset_level_lte()
        )
        limitation.add_level()
        limitation.max_array_size = len(self.value) * 2 + 1
        return limitation

    def verify(self, value: dict | list):
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)

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


class BaseNestedGenericArrayNot(
    BaseNestedNot,
    BaseGenericArrayPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
    ABC,
):
    value: list[_t_SpecifiedType]

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = (
            self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).calculate_limitations().reset_level_lte()
        )
        limitation.add_level()
        limitation.max_array_size = len(self.value) * 2 + 1
        return limitation

    def verify(self, value: list):
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)
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


class BaseNestedGenericObject(
    BaseNested,
    BaseGenericObjectPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
    ABC,
):
    value: dict[
        Union[
            't_Predicate',
            str,
        ],
        _t_SpecifiedType,
    ]

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = (
            self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).calculate_limitations().reset_level_lte()
        )
        limitation.add_level()
        return limitation

    def verify(self, value: dict | list):
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)
        if main_predicate.verify(value):
            return True

        if isinstance(value, list):
            for item in value:
                if isinstance(item, dict) and self.verify(item):
                    return True
        elif isinstance(value, dict):
            for k, v in value.items():
                if isinstance(v, dict):
                    if self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).verify(v):
                        return True
                    elif self.verify(v):
                        return True
                if isinstance(v, list) and self.verify(v):
                    return True
        return False


class BaseNestedGenericObjectNot(
    BaseNestedNot,
    BaseGenericObjectPredicate[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
    ABC,
):
    # value: dict[
    #     Union[
    #         Annotated['t_Predicate', Field(discriminator='type_of')],
    #         str,
    #     ],
    #     _t_SpecifiedType,
    # ]
    value: dict[
        Union[
            't_Predicate',
            str,
        ],
        _t_SpecifiedType,
    ]

    def calculate_limitations(self) -> PredicateLimitations:
        limitation = (
            self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).calculate_limitations().reset_level_lte()
        )
        limitation.add_level()
        return limitation

    def verify(self, value: dict):
        main_predicate = self.sub_predicate(value=self.value, **self.sub_predicate_kwargs)
        if main_predicate.verify(value):
            return True

        if not isinstance(value, dict):
            return False

        for k, v in value.items():
            if isinstance(v, dict):
                if not self.sub_predicate(value=self.value, **self.sub_predicate_kwargs).verify(v):
                    return False
                elif not self.verify(v):
                    return False
            if isinstance(v, list):
                for item in v:
                    if isinstance(item, dict) and not self.verify(item):
                        return False
        return True


class GenericNestedObjectEqualTo(
    BaseNestedGenericObject[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-object-equal-to'] = '$-mockau-nested-object-equal-to'

    @property
    def sub_predicate(self):
        from core.predicates import ObjectEqualTo

        return ObjectEqualTo

    def __invert__(self):
        from core.predicates import NestedObjectNotEqualTo

        return NestedObjectNotEqualTo(value=self.value)


class GenericNestedObjectNotEqualTo(
    BaseNestedGenericObjectNot[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-object-not-equal-to'] = '$-mockau-nested-object-not-equal-to'

    @property
    def sub_predicate(self):
        from core.predicates import ObjectNotEqualTo

        return ObjectNotEqualTo

    def __invert__(self):
        from core.predicates import NestedObjectEqualTo

        return NestedObjectEqualTo(value=self.value)


class GenericNestedObjectContainsSubset(
    BaseNestedGenericObject[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-object-contains'] = '$-mockau-nested-object-contains'

    @property
    def sub_predicate(self):
        from core.predicates import ObjectContainsSubset

        return ObjectContainsSubset

    def __invert__(self):
        from core.predicates import NestedObjectNotContainsSubset

        return NestedObjectNotContainsSubset(value=self.value)


class GenericNestedObjectNotContainsSubset(
    BaseNestedGenericObjectNot[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-object-not-contains'] = '$-mockau-nested-object-not-contains'

    @property
    def sub_predicate(self):
        from core.predicates import ObjectNotContainsSubset

        return ObjectNotContainsSubset

    def __invert__(self):
        from core.predicates import NestedObjectContainsSubset

        return NestedObjectContainsSubset(value=self.value)


class GenericNestedArrayEqualTo(
    BaseNestedGenericArray[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-array-equal-to'] = '$-mockau-nested-array-equal-to'
    ignore_order: bool = False

    @property
    def sub_predicate(self):
        from core.predicates import ArrayEqualTo

        return ArrayEqualTo

    @property
    def sub_predicate_kwargs(self):
        return {'ignore_order': self.ignore_order}

    def __invert__(self):
        from core.predicates import NestedArrayNotEqualTo

        return NestedArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)


class GenericNestedArrayNotEqualTo(
    BaseNestedGenericArrayNot[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-array-not-equal-to'] = '$-mockau-nested-array-not-equal-to'
    ignore_order: bool = False

    @property
    def sub_predicate(self):
        from core.predicates import ArrayNotEqualTo

        return ArrayNotEqualTo

    @property
    def sub_predicate_kwargs(self):
        return {'ignore_order': self.ignore_order}

    def __invert__(self):
        from core.predicates import NestedArrayEqualTo

        return NestedArrayEqualTo(value=self.value, ignore_order=self.ignore_order)


class GenericNestedArrayContains(
    BaseNestedGenericArray[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-array-contains'] = '$-mockau-nested-array-contains'

    @property
    def sub_predicate(self):
        from core.predicates import ArrayContains

        return ArrayContains

    def __invert__(self):
        from core.predicates import NestedArrayNotContains

        return NestedArrayNotContains(value=self.value)


class GenericNestedArrayNotContains(
    BaseNestedGenericArrayNot[_t_SpecifiedType],
    Generic[_t_SpecifiedType],
):
    type_of: Literal['$-mockau-nested-array-not-contains'] = '$-mockau-nested-array-not-contains'

    @property
    def sub_predicate(self):
        from core.predicates import ArrayNotContains

        return ArrayNotContains

    def __invert__(self):
        from core.predicates import NestedArrayContains

        return NestedArrayContains(value=self.value)
