from functools import reduce
from typing import Any, Literal

import z3

from core.predicates.base_predicate import BaseLogicalPredicate, BaseScalarPredicate, PredicateType, VariableContext


class AnyPredicate(BaseScalarPredicate):
    type_of: Literal['AnyPredicate'] = 'AnyPredicate'

    def is_matched(self, value: Any) -> bool:
        return True

    @property
    def predicate_types(self):
        return {PredicateType.Any}

    def to_z3(self, ctx):
        return z3.BoolVal(True)


class NotPredicate(BaseLogicalPredicate):
    type_of: Literal['NotPredicate'] = 'NotPredicate'
    predicate: Any

    @property
    def predicate_types(self) -> PredicateType:
        return self.predicate.predicate_types

    def to_z3(self, ctx: VariableContext):
        return z3.Not(self.predicate.to_z3(ctx))


class AndPredicate(BaseLogicalPredicate):
    type_of: Literal['AndPredicate'] = 'AndPredicate'
    predicates: list

    @property
    def predicate_types(self) -> set[PredicateType]:
        common_types = reduce(lambda x, y: x & y, [p.predicate_types for p in self.predicates])
        if common_types:
            return common_types
        else:
            return {PredicateType.Null}

    def to_z3(self, ctx: VariableContext):
        if self.predicate_types == {PredicateType.Null}:
            return z3.BoolVal(False)
        else:
            return z3.And([p.to_z3(ctx) for p in self.predicates])


class OrPredicate(BaseLogicalPredicate):
    type_of: Literal['OrPredicate'] = 'OrPredicate'
    predicates: list

    @property
    def predicate_types(self) -> set[PredicateType]:
        return set.union(*[p.predicate_types for p in self.predicates])

    def to_z3(self, ctx: VariableContext):
        return z3.Or([p.to_z3(ctx) for p in self.predicates])
