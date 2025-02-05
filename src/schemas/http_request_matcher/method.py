from core.http.interaction.common import HttpMethod
from schemas.matchers.variable_matcher import SetVariableMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class MethodOrMatcher(SetVariableMatcher):
    any_of: list[HttpMethod]

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if value in self.any_of:
            return self.is_variable_matched(value, context=context)
        return False


class MethodEqualToMatcher(SetVariableMatcher):
    equal_to: HttpMethod

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if value == self.equal_to:
            return self.is_variable_matched(value, context=context)
        return False


t_MethodMatcher = MethodOrMatcher | MethodEqualToMatcher
