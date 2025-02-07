from abc import abstractmethod

from core.bases.base_schema import BaseSchema
from core.plain_matchers.types import t_PlainMatcher
from schemas.variables import VariablesContext


class AbstractMatcher(BaseSchema):
    @abstractmethod
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        pass

    @abstractmethod
    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        pass
