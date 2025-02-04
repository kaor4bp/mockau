from abc import abstractmethod
from typing import Generic, TypeVar

from schemas.base_schema import BaseSchema
from schemas.variables import VariablesContext, variables_context_transaction


class AbstractMatcher(BaseSchema):
    @abstractmethod
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        pass


t_Matcher = TypeVar('t_Matcher', bound=AbstractMatcher)


class BaseAllOfMatcher(AbstractMatcher, Generic[t_Matcher]):
    all_of: list[t_Matcher]

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


class BaseAnyOfMatcher(AbstractMatcher, Generic[t_Matcher]):
    any_of: list[t_Matcher]

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False
