from elasticsearch_dsl import Keyword

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.actions.common import ActionReference


class ActionReferenceInnerDocument(BaseModelInnerDocument):
    action_id: str = Keyword()
    action_revision: str = Keyword()

    @classmethod
    def from_model(cls, model: ActionReference) -> 'ActionReferenceInnerDocument':
        return cls(action_id=str(model.action_id), action_revision=str(model.action_revision))

    def to_model(self) -> ActionReference:
        return ActionReference(action_id=self.action_id, action_revision=self.action_revision)
