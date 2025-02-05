from typing import Optional

from elasticsearch_dsl import Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.models import HttpRequestResponseViewEventModel
from core.http.interaction.documents.http_request_inner_document import HttpRequestInnerDocument
from core.http.interaction.documents.http_response_inner_document import HttpResponseInnerDocument
from settings import MockauSettings


class HttpRequestResponseViewEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_response_view'

    http_request: HttpRequestInnerDocument = Object(doc_class=HttpRequestInnerDocument, required=True)
    http_response: Optional[HttpResponseInnerDocument] = Object(doc_class=HttpResponseInnerDocument, required=False)

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
        )

    def to_model(self) -> HttpRequestResponseViewEventModel:
        return HttpRequestResponseViewEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            http_request=self.http_request.to_http_request(),
            http_response=self.http_response.to_http_response() if self.http_response else None,
        )
