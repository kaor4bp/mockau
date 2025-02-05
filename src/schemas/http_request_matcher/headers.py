from typing import Optional

from pydantic import Field

from core.http.interaction.schemas import HttpQueryParam
from schemas.matchers.abstract_matcher import AbstractMatcher, BaseAllOfMatcher, BaseAnyOfMatcher
from schemas.matchers.string_matcher import t_StringMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class HeaderValueOrMatcher(BaseAnyOfMatcher):
    any_of: list[t_StringMatcher]


class HeaderValuesAndMatcher(BaseAllOfMatcher):
    all_of: list[t_StringMatcher]


class HeaderItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    values: Optional[HeaderValueOrMatcher | HeaderValuesAndMatcher] = Field(default=None)

    @variables_context_transaction
    def is_matched(self, value: list[HttpQueryParam], *, context: VariablesContext) -> bool:
        for param in value:
            if not self.key.is_matched(param.key, context=context):
                continue

            if self.values:
                return self.values.is_matched(param.value, context=context)
            else:
                return True
        else:
            return False


class HeaderOrMatcher(BaseAnyOfMatcher):
    any_of: list['t_HeaderMatcherContainer'] = Field(
        examples=[
            [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        ]
    )


class HeaderAndMatcher(BaseAllOfMatcher):
    all_of: list['t_HeaderMatcherContainer'] = Field(
        # examples=[
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'contains': 'json'}]}}],
        # ]
    )


t_HeaderMatcherContainer = HeaderAndMatcher | HeaderOrMatcher | HeaderItemMatcher
