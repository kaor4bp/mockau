from typing import Optional

from elasticsearch_dsl import Keyword, Object

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.inner_documents import HttpRequestInnerDocument
from core.http.events.models import HttpRequestEventModel
from settings import MockauSettings


class HttpRequestEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request'

    parent_minow_traceparent: Optional[str] = Keyword(required=False)
    http_request: HttpRequestInnerDocument = Object(doc_class=HttpRequestInnerDocument, required=True)

    @classmethod
    def from_model(cls, model: HttpRequestEventModel) -> 'HttpRequestEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            minow_traceparent=model.minow_traceparent,
            minow_trace_id=model.minow_trace_id,
            timestamp=model.timestamp,
            parent_minow_traceparent=model.parent_minow_traceparent,
            http_request=HttpRequestInnerDocument.from_model(model.http_request),
            traceparent=model.traceparent,
            level=model.level,
        )

    def to_model(self) -> HttpRequestEventModel:
        return HttpRequestEventModel(
            event=self.event,
            created_at=self.created_at,
            minow_traceparent=self.minow_traceparent,
            parent_minow_traceparent=self.parent_minow_traceparent,
            http_request=self.http_request.to_model(),
            traceparent=self.traceparent,
            level=self.level,
        )
