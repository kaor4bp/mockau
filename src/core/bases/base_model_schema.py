from abc import abstractmethod
from typing import Type, TypeVar

from core.bases.base_model import BaseModel
from core.bases.base_schema import BaseSchema

_t_Schema = TypeVar('_t_Schema', bound='BaseModelSchema')
_t_Model = TypeVar('_t_Model', bound=BaseModel)


class BaseModelSchema(BaseSchema):
    @classmethod
    @abstractmethod
    def from_model(cls: Type[_t_Schema], model: _t_Model) -> _t_Schema:
        pass

    @abstractmethod
    def to_model(self) -> _t_Model:
        pass
