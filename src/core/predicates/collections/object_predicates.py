import itertools
from typing import Any, Self

import z3
from pydantic import model_validator

from core.predicates.base_predicate import BaseCollectionPredicate, BasePredicate, PredicateType, VariableContext
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
        object_var = ctx.get_variable(predicate_type=PredicateType.Object)
        all_keys = z3.EmptySet(z3.StringSort())
        all_keys_list = []
        constraints = []

        for key_predicate, value_predicate in self.value.items():
            key_ctx = ctx.create_child_context()
            value_ctx = ctx.create_child_context()
            ctx.push_to_global_constraints(key_predicate.to_z3(key_ctx))
            constraints.append(value_predicate.to_z3(value_ctx))

            key_var = key_ctx.get_variable(PredicateType.String)
            all_keys_list.append(key_var)
            all_keys = z3.SetAdd(all_keys, key_var)
            ctx.push_to_global_constraints(z3.Select(object_var, key_var) == value_ctx.json_type_variable)

        if isinstance(self, ObjectContainsSubset):
            constraints += [
                ctx.JsonType.get_object_keys_quantity(ctx.json_type_variable) >= z3.IntVal(len(self.value.keys())),
                z3.IsSubset(all_keys, ctx.JsonType.get_object_keys(ctx.json_type_variable)),
            ]
        elif isinstance(self, ObjectEqualTo):
            constraints += [
                ctx.JsonType.get_object_keys_quantity(ctx.json_type_variable) == z3.IntVal(len(self.value.keys())),
                ctx.JsonType.get_object_keys(ctx.json_type_variable) == all_keys,
            ]
        else:
            raise NotImplementedError(f'to_z3 for ObjectPredicate {self} not implemented yet')

        constraints += [
            z3.Distinct(object_var),
            z3.Distinct(all_keys),
        ]

        return z3.And(*constraints)


class ObjectEqualTo(BaseObjectPredicate):
    pass


class ObjectContainsSubset(BaseObjectPredicate):
    pass
