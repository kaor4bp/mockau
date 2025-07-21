import z3

from core.predicates.base_predicate import BasePredicate
from core.predicates.consts import PredicateType
from core.predicates.context.variable_context import VariableContext


class BasePredicateGroup(BasePredicate):
    def verify(self, value):
        return self.compile_predicate().verify(value)

    def to_z3(self, ctx: VariableContext) -> z3.ExprRef:
        return self.compile_predicate().to_z3(ctx)

    @property
    def predicate_types(self) -> set[PredicateType]:
        return {PredicateType.Object}

    def compile_predicate(self):
        from core.predicates import ObjectContainsSubset

        result = {}

        for field_name in self.model_fields_set:
            field_value = getattr(self, field_name)
            if isinstance(field_value, BasePredicate):
                field_value = field_value.compile_predicate()
            result[field_name] = field_value

        return ObjectContainsSubset(value=result)
