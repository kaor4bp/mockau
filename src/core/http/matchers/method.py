from core.deprecated_matchers.variable_matcher import SetVariableMatcher
from core.http.interaction.common import HttpMethod
from core.predicates import OrPredicate, StringEqualTo, t_Predicate
from schemas.variables import VariablesContext, variables_context_transaction


class MethodOrMatcher(SetVariableMatcher):
    any_of: list[HttpMethod]

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if value in self.any_of:
            return self.is_variable_matched(value, context=context)
        return False

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        return OrPredicate(predicates=[StringEqualTo(value=item.value) for item in self.any_of])


class MethodEqualToMatcher(SetVariableMatcher):
    equal_to: HttpMethod

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if value == self.equal_to:
            return self.is_variable_matched(value, context=context)
        return False

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        return StringEqualTo(value=self.equal_to.value)


t_MethodMatcher = MethodOrMatcher | MethodEqualToMatcher
