from elasticsearch_dsl import Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.inner_documents import HttpResponseInnerDocument
from core.http.events.models import HttpResponseEventModel
from settings import MockauSettings


class HttpResponseEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_response'

    http_response: HttpResponseInnerDocument = Object(doc_class=HttpResponseInnerDocument, required=True)

    @classmethod
    def from_model(cls, model: HttpResponseEventModel) -> 'HttpResponseEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            http_response=HttpResponseInnerDocument.from_model(model.http_response),
            traceparent=model.traceparent,
            level=model.level,
        )

    def to_model(self) -> HttpResponseEventModel:
        return HttpResponseEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            http_response=self.http_response.to_model(),
            traceparent=self.traceparent,
            level=self.level,
        )
