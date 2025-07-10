from abc import abstractmethod

from core.bases.base_schema import BaseSchema
from core.predicates import t_Predicate
from schemas.variables import VariablesContext


class AbstractMatcher(BaseSchema):
    @abstractmethod
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        pass

    @abstractmethod
    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        pass
