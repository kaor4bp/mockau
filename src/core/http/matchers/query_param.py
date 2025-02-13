from pydantic import Field

from core.http.interaction.schemas import HttpQueryParam
from core.matchers.abstract_matcher import AbstractMatcher
from core.matchers.string_matcher import t_StringMatcher
from core.plain_matchers.object_plain_matchers import ObjectAnd, ObjectOr, ObjectPlainMatcher
from core.plain_matchers.types import t_PlainMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class QueryParamItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    value: t_StringMatcher | None = Field(default=None)

    @variables_context_transaction
    def is_matched(self, values: list[HttpQueryParam], *, context: VariablesContext) -> bool:
        for param in values:
            if not self.key.is_matched(param.key, context=context):
                continue

            if self.value:
                return self.value.is_matched(param.value, context=context)
            else:
                return True
        else:
            return False

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        object_plain_matcher = {'key': self.key.to_plain_matcher(context=context)}
        if self.value:
            object_plain_matcher['value'] = self.value.to_plain_matcher(context=context)
        return ObjectPlainMatcher(
            obj=object_plain_matcher,
            obj_name=f'{self.__class__.__module__}#{self.__class__.__name__}',
        )


class QueryParamAndMatcher(AbstractMatcher):
    all_of: list['t_QueryParamMatcherContainer']

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return ObjectAnd(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.all_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


class QueryParamOrMatcher(AbstractMatcher):
    any_of: list['t_QueryParamMatcherContainer']

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return ObjectOr(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.any_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False


t_QueryParamMatcherContainer = QueryParamAndMatcher | QueryParamOrMatcher | QueryParamItemMatcher
