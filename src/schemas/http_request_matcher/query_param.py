from pydantic import Field

from schemas.http_request.http_parts import HttpRequestQueryParam
from schemas.matchers.abstract_matcher import AbstractMatcher, BaseAllOfMatcher, BaseAnyOfMatcher
from schemas.matchers.string_matcher import t_StringMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class QueryParamItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    value: t_StringMatcher | None = Field(default=None)

    @variables_context_transaction
    def is_matched(self, values: list[HttpRequestQueryParam], *, context: VariablesContext) -> bool:
        for param in values:
            if not self.key.is_matched(param.key, context=context):
                continue

            if self.value:
                return self.value.is_matched(param.value, context=context)
            else:
                return True
        else:
            return False


class QueryParamAndMatcher(BaseAllOfMatcher['t_QueryParamMatcherContainer']):
    all_of: list['t_QueryParamMatcherContainer']


class QueryParamOrMatcher(BaseAnyOfMatcher['t_QueryParamMatcherContainer']):
    any_of: list['t_QueryParamMatcherContainer']


t_QueryParamMatcherContainer = QueryParamAndMatcher | QueryParamOrMatcher | QueryParamItemMatcher
