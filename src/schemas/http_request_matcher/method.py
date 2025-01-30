from schemas.http_request.http_parts import HttpMethod
from schemas.matchers.abstract_matcher import AbstractMatcher, BaseAnyOfMatcher
from schemas.variables import t_Variable
from schemas.variables_context import VariablesContext, variables_context_transaction


class MethodOrMatcher(BaseAnyOfMatcher):
    any_of: list[HttpMethod]
    variable: t_Variable | None = None

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if super().is_matched(value, context=context):
            if self.variable is not None:
                return self.variable.is_matched(value, context=context)
            else:
                return True
        return False


class MethodEqualToMatcher(AbstractMatcher):
    equal_to: HttpMethod

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        return value == self.equal_to


t_MethodMatcher = MethodOrMatcher | MethodEqualToMatcher
