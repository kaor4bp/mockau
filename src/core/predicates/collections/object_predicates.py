import itertools
from typing import Any, Generator, Self

import z3
from pydantic import model_validator

from core.predicates.base_predicate import (
    BaseCollectionPredicate,
    BasePredicate,
    ObjectContext,
    PredicateType,
    VariableContext,
)
from core.predicates.helpers import value_to_predicate


def generate_unique_permutations(elements):
    all_permutations = itertools.permutations(elements)
    unique_permutations_set = set()
    for p in all_permutations:
        unique_permutations_set.add(p)
    return [list(p) for p in unique_permutations_set]


class BaseObjectPredicate(BaseCollectionPredicate):
    value: dict

    @model_validator(mode='after')
    def handle_nested_objects(self) -> Self:
        for k, v in list(self.value.items()):
            if not isinstance(k, BasePredicate):
                new_k = value_to_predicate(k)
                self.value[new_k] = self.value.pop(k)
                k = new_k
            if not isinstance(v, BasePredicate):
                self.value[k] = value_to_predicate(v)
        return self

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Object}

    def is_matched(self, value: Any) -> bool:
        pass

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        constraints = []
        for constraint in self.to_z3_iter(ctx):
            constraints.append(constraint)
        return z3.Or(constraints)

    def to_z3_iter(self, ctx: VariableContext) -> Generator[z3.ExprRef, None, None]:
        object_var: ObjectContext = ctx.get_variable(predicate_type=PredicateType.Object)

        extra_quantities = [0]
        if isinstance(self, ObjectContainsSubset):
            for i in range(10 - len(self.value.keys())):
                extra_quantities.append(i + 1)

        for extra_quantity in extra_quantities:
            all_keys = list(self.value.keys())

            if isinstance(self, ObjectContainsSubset):
                all_keys = list(self.value.keys()) + ['any' for _ in range(extra_quantity)]

            all_keys_set = z3.EmptySet(z3.StringSort())
            for index, key in enumerate(self.value.keys()):
                key_var = object_var.get_key_context(index)
                all_keys_set = z3.SetAdd(all_keys_set, key_var.get_variable(PredicateType.String))

            for keys in generate_unique_permutations(all_keys):
                local_constraints = [z3.Distinct(all_keys_set)]
                values_iterators = []

                for key_index, key in enumerate(keys):
                    if isinstance(key, str):
                        object_var.get_value_context(key_index)
                        object_var.get_type_sequence_var(key_index)
                        object_var.get_key_context(key_index)
                        continue

                    key_var = object_var.get_key_context(key_index)
                    local_constraints.append(z3.Length(key_var.get_variable(PredicateType.String)) < 20)
                    local_constraints.append(key.to_z3(key_var))

                    val = self.value[key]
                    val_var = object_var.get_value_context(key_index)

                    type_val = z3.EmptySet(z3.StringSort())
                    for pt in val.predicate_types:
                        if pt is PredicateType.String:
                            local_constraints.append(z3.Length(val_var.get_variable(pt)) < 20)
                        type_val = z3.SetAdd(type_val, z3.StringVal(pt.value))
                    intersection = z3.SetIntersect(type_val, object_var.get_type_sequence_var(key_index))
                    local_constraints.append(z3.Not(intersection == z3.EmptySet(z3.StringSort())))

                    local_constraints.append(val.to_z3(val_var))

                if isinstance(self, ObjectEqualTo):
                    local_constraints.append(object_var.all_keys_variable == all_keys_set)
                    local_constraints.append(object_var.all_keys_quantity_variable == z3.IntVal(len(keys)))
                    # intersection = z3.SetIntersect(object_var.all_keys_variable, all_keys_set)
                    # difference = z3.SetDifference(object_var.all_keys_variable, all_keys_set)
                    # local_constraints.append(intersection == all_keys_set)
                    # local_constraints.append(difference == z3.EmptySet(z3.StringSort()))
                elif isinstance(self, ObjectContainsSubset):
                    local_constraints.append(z3.IsSubset(all_keys_set, object_var.all_keys_variable))
                    local_constraints.append(object_var.all_keys_quantity_variable == z3.IntVal(len(keys)))
                else:
                    raise AssertionError('Unsupported predicate')

                if not values_iterators:
                    yield z3.And(*local_constraints)
                else:
                    for sub_local_constraints in itertools.product(*values_iterators):
                        yield z3.And(*local_constraints, *sub_local_constraints)


class ObjectEqualTo(BaseObjectPredicate):
    pass


class ObjectContainsSubset(BaseObjectPredicate):
    pass
