from abc import abstractmethod
from typing import Type, TypeVar

from elasticsearch_dsl import AsyncDocument

from core.bases.base_model import BaseModel

_t_Document = TypeVar('_t_Document', bound=AsyncDocument)
_t_Model = TypeVar('_t_Model', bound='BaseDocumentModel')


class BaseDocumentModel(BaseModel):
    @classmethod
    @abstractmethod
    def from_document(cls: Type[_t_Model], document: _t_Document) -> _t_Model:
        pass

    @abstractmethod
    def to_document(self) -> _t_Document:
        pass
