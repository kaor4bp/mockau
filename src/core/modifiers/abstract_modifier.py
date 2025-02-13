from abc import abstractmethod

from core.bases.base_schema import BaseSchema
from schemas.variables import VariablesContext


class AbstractModifier(BaseSchema):
    @abstractmethod
    def modify(self, value, *, context: VariablesContext):
        pass
