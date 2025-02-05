from abc import abstractmethod

from core.bases.base_schema import BaseSchema


class AbstractModifier(BaseSchema):
    @abstractmethod
    def modify(self, value):
        pass
