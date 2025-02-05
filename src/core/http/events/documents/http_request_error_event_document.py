from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.models import HttpRequestErrorEventModel
from settings import MockauSettings


class HttpRequestErrorEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_error'

    @classmethod
    def from_model(cls, model: HttpRequestErrorEventModel) -> 'HttpRequestErrorEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
        )

    def to_model(self) -> HttpRequestErrorEventModel:
        return HttpRequestErrorEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
        )
