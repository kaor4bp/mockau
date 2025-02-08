from elasticsearch_dsl import Keyword

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.actions.common import ActionReference
from core.http.interaction.schemas import HttpHeaders


class HttpHeaderInnerDocument(BaseModelInnerDocument):
    key: str = Keyword()
    values: list[str] = Keyword(multi=True)

    @classmethod
    def from_model(cls, model: HttpHeaders) -> 'list[HttpHeaderInnerDocument]':
        results = []
        for key, values in model.model_dump(mode='json').items():
            results.append(cls(key=key, values=values))
        return results

    def to_model(self) -> ActionReference:
        return ActionReference(action_id=self.action_id, action_revision=self.action_revision)
