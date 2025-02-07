from elasticsearch_dsl import Object, Text

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.inner_documents import ActionReferenceInnerDocument
from core.http.events.models import HttpRequestActionNotMatchedViewEventModel
from settings import MockauSettings


class HttpRequestActionNotMatchedViewEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_action_not_matched'

    action_reference: ActionReferenceInnerDocument = Object(
        doc_class=ActionReferenceInnerDocument,
        required=True,
    )
    description: str = Text(required=True)

    @classmethod
    def from_model(
        cls, model: HttpRequestActionNotMatchedViewEventModel
    ) -> 'HttpRequestActionNotMatchedViewEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            description=model.description,
            action_reference=ActionReferenceInnerDocument.from_model(model.action_reference),
        )

    def to_model(self) -> HttpRequestActionNotMatchedViewEventModel:
        return HttpRequestActionNotMatchedViewEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            description=self.description,
            action_reference=self.action_reference.to_model(),
        )
