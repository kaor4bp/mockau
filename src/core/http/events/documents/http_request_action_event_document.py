from elasticsearch_dsl import Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.inner_documents import ActionReferenceInnerDocument
from core.http.events.models import HttpRequestActionEventModel
from settings import MockauSettings


class HttpRequestActionEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_action'

    action_reference: ActionReferenceInnerDocument = Object(
        doc_class=ActionReferenceInnerDocument,
        required=True,
    )

    @classmethod
    def from_model(cls, model: HttpRequestActionEventModel) -> 'HttpRequestActionEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            action_reference=ActionReferenceInnerDocument.from_model(model.action_reference),
            traceparent=model.traceparent,
            level=model.level,
        )

    def to_model(self) -> HttpRequestActionEventModel:
        return HttpRequestActionEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            action_reference=self.action_reference.to_model(),
            traceparent=self.traceparent,
            level=self.level,
        )
