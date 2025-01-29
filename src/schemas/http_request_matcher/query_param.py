from pydantic import Field

from schemas.common_matchers.abstract_matcher import AbstractMatcher, AndMatcher, OrMatcher
from schemas.common_matchers.string_matcher import t_StringMatcher
from schemas.http_request.http_parts import HttpRequestQueryParam


class QueryParamItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    value: t_StringMatcher | None = Field(default=None)

    def is_matched(self, values: list[HttpRequestQueryParam]) -> bool:
        for param in values:
            if not self.key.is_matched(param.key):
                continue

            if self.value:
                return self.value.is_matched(param.value)
            else:
                return True
        else:
            return False


class QueryParamAndMatcher(AndMatcher['t_QueryParamMatcherContainer']):
    and_: list['t_QueryParamMatcherContainer']


class QueryParamOrMatcher(OrMatcher['t_QueryParamMatcherContainer']):
    or_: list['t_QueryParamMatcherContainer']


t_QueryParamMatcherContainer = QueryParamAndMatcher | QueryParamOrMatcher | QueryParamItemMatcher
