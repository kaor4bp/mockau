from typing import Optional

from elasticsearch_dsl import Float, Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.inner_documents import HttpRequestInnerDocument, HttpResponseInnerDocument
from core.http.events.models import HttpRequestResponseViewEventModel
from settings import MockauSettings


class HttpRequestResponseViewEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_response_view'

    http_request: HttpRequestInnerDocument = Object(doc_class=HttpRequestInnerDocument, required=True)
    http_response: Optional[HttpResponseInnerDocument] = Object(doc_class=HttpResponseInnerDocument, required=False)
    elapsed: float = Float()
    processing_time: float = Float()

    @classmethod
    def from_model(cls, model: HttpRequestResponseViewEventModel) -> 'HttpRequestResponseViewEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            http_request=HttpRequestInnerDocument.from_model(model.http_request),
            http_response=HttpResponseInnerDocument.from_model(model.http_response) if model.http_response else None,
            traceparent=model.traceparent,
            processing_time=model.processing_time,
            elapsed=model.elapsed,
            level=model.level,
        )

    def to_model(self) -> HttpRequestResponseViewEventModel:
        return HttpRequestResponseViewEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            http_request=self.http_request.to_http_request(),
            http_response=self.http_response.to_http_response() if self.http_response else None,
            traceparent=self.traceparent,
            processing_time=self.processing_time,
            elapsed=self.elapsed,
            level=self.level,
        )
