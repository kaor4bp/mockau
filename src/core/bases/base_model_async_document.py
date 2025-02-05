from abc import abstractmethod
from typing import Type, TypeVar

from elasticsearch_dsl import AsyncDocument

from core.bases.base_model import BaseModel

_t_Document = TypeVar('_t_Document', bound='BaseModelAsyncDocument')
_t_Model = TypeVar('_t_Model', bound=BaseModel)


class BaseModelAsyncDocument(AsyncDocument):
    @classmethod
    @abstractmethod
    def from_model(cls: Type[_t_Document], model: _t_Model) -> _t_Document:
        pass

    @abstractmethod
    def to_model(self) -> _t_Model:
        pass
