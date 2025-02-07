from typing import Optional

from pydantic import Field

from core.http.interaction.schemas import HttpQueryParam
from core.matchers.abstract_matcher import AbstractMatcher
from core.matchers.string_matcher import t_StringMatcher
from core.plain_matchers.object_plain_matchers import ObjectAnd, ObjectOr, ObjectPlainMatcher
from core.plain_matchers.string_plain_matchers import StringAnd, StringOr
from core.plain_matchers.types import t_PlainMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class HeaderValueOrMatcher(AbstractMatcher):
    any_of: list[t_StringMatcher]

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return StringOr(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.any_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False


class HeaderValuesAndMatcher(AbstractMatcher):
    all_of: list[t_StringMatcher]

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return StringAnd(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.all_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


class HeaderItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    values: Optional[HeaderValueOrMatcher | HeaderValuesAndMatcher] = Field(default=None)

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        object_plain_matcher = {'key': self.key.to_plain_matcher(context=context)}
        if self.values:
            object_plain_matcher['values'] = self.values.to_plain_matcher(context=context)
        return ObjectPlainMatcher(
            obj=object_plain_matcher,
            obj_name=f'{self.__class__.__module__}#{self.__class__.__name__}',
        )

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


class HeaderOrMatcher(AbstractMatcher):
    any_of: list['t_HeaderMatcherContainer'] = Field(
        examples=[
            [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        ]
    )

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return ObjectOr(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.any_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False


class HeaderAndMatcher(AbstractMatcher):
    all_of: list['t_HeaderMatcherContainer'] = Field(
        # examples=[
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'equal_to': 'application/json'}]}}],
        #     [{'key': {'equal_to': 'content-type'}, 'values': {'any_of': [{'contains': 'json'}]}}],
        # ]
    )

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return ObjectAnd(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.all_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


t_HeaderMatcherContainer = HeaderAndMatcher | HeaderOrMatcher | HeaderItemMatcher
