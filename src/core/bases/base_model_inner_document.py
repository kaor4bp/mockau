from abc import abstractmethod
from typing import Type, TypeVar

from elasticsearch_dsl import InnerDoc

from core.bases.base_model import BaseModel

_t_InnerDocument = TypeVar('_t_InnerDocument', bound='BaseModelInnerDocument')
_t_Model = TypeVar('_t_Model', bound=BaseModel)


class BaseModelInnerDocument(InnerDoc):
    @classmethod
    @abstractmethod
    def from_model(cls: Type[_t_InnerDocument], model: _t_Model) -> _t_InnerDocument:
        pass

    @abstractmethod
    def to_model(self) -> _t_Model:
        pass
