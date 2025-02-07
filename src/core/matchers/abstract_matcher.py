from abc import abstractmethod
from typing import Generic, TypeVar

from core.bases.base_schema import BaseSchema
from core.plain_matchers.common_plain_matchers import And, Or
from core.plain_matchers.types import t_PlainMatcher
from schemas.variables import VariablesContext, variables_context_transaction


class AbstractMatcher(BaseSchema):
    @abstractmethod
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        pass

    @abstractmethod
    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        pass


t_Matcher = TypeVar('t_Matcher', bound=AbstractMatcher)


class BaseAllOfMatcher(AbstractMatcher, Generic[t_Matcher]):
    all_of: list[t_Matcher]

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return And(*[matcher.to_plain_matcher(context=context) for matcher in self.all_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


class BaseAnyOfMatcher(AbstractMatcher, Generic[t_Matcher]):
    any_of: list[t_Matcher]

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        return Or(*[matcher.to_plain_matcher(context=context) for matcher in self.any_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False
