from abc import abstractmethod

from schemas.base_schema import BaseSchema


class AbstractModifier(BaseSchema):
    @abstractmethod
    def modify(self, value):
        pass
