from typing import Optional

from elasticsearch_dsl import Keyword, Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.models import HttpRequestEventModel
from core.http.interaction.documents.http_request_inner_document import HttpRequestInnerDocument
from settings import MockauSettings


class HttpRequestEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request'

    parent_mockau_traceparent: Optional[str] = Keyword(required=False)
    http_request: HttpRequestInnerDocument = Object(doc_class=HttpRequestInnerDocument, required=True)

    @classmethod
    def from_model(cls, model: HttpRequestEventModel) -> 'HttpRequestEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            parent_mockau_traceparent=model.parent_mockau_traceparent,
            http_request=HttpRequestInnerDocument.from_model(model.http_request),
        )

    def to_model(self) -> HttpRequestEventModel:
        return HttpRequestEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            parent_mockau_traceparent=self.parent_mockau_traceparent,
            http_request=self.http_request.to_model(),
        )
