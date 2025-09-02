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
            minow_traceparent=model.minow_traceparent,
            minow_trace_id=model.minow_trace_id,
            timestamp=model.timestamp,
            traceparent=model.traceparent,
            level=model.level,
        )

    def to_model(self) -> HttpRequestErrorEventModel:
        return HttpRequestErrorEventModel(
            event=self.event,
            created_at=self.created_at,
            minow_traceparent=self.minow_traceparent,
            traceparent=self.traceparent,
            level=self.level,
        )
