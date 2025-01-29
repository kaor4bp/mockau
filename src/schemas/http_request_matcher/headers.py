from typing import Optional

from pydantic import Field

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.common_matchers.string_matcher import t_StringMatcher
from schemas.http_request.http_parts import HttpRequestQueryParam


class HeaderValueOrMatcher(AbstractMatcher):
    any_of: list[t_StringMatcher]

    def is_matched(self, value) -> bool:
        for item in self.any_of:
            if item.is_matched(value):
                return True
        return False


class HeaderValuesAndMatcher(AbstractMatcher):
    all_of: list[t_StringMatcher]

    def is_matched(self, value) -> bool:
        for item in self.all_of:
            if not item.is_matched(value):
                return False
        return True


class HeaderItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    values: Optional[HeaderValueOrMatcher | HeaderValuesAndMatcher] = Field(default=None)

    def is_matched(self, value: list[HttpRequestQueryParam]) -> bool:
        for param in value:
            if not self.key.is_matched(param.key):
                continue

            if self.values:
                return self.values.is_matched(param.value)
            else:
                return True
        else:
            return False


class HeaderOrMatcher(AbstractMatcher):
    any_of: list['t_HeaderMatcherContainer'] = Field(
        examples=[
            [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        ]
    )

    def is_matched(self, value) -> bool:
        for item in self.any_of:
            if item.is_matched(value):
                return True
        return False


class HeaderAndMatcher(AbstractMatcher):
    all_of: list['t_HeaderMatcherContainer'] = Field(
        # examples=[
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'contains': 'json'}]}}],
        # ]
    )

    def is_matched(self, value) -> bool:
        for item in self.all_of:
            if not item.is_matched(value):
                return False
        return True


t_HeaderMatcherContainer = HeaderAndMatcher | HeaderOrMatcher | HeaderItemMatcher
