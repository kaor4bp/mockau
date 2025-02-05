from elasticsearch_dsl import Keyword

from core.http.events.documents.base_http_event_document import BaseHttpEventDocument
from core.http.events.models import HttpRequestActionEventModel
from settings import MockauSettings


class HttpRequestActionEventDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_action'

    action_id: str = Keyword(required=True)

    @classmethod
    def from_model(cls, model: HttpRequestActionEventModel) -> 'HttpRequestActionEventDocument':
        return cls(
            event=model.event.value,
            created_at=model.created_at,
            mockau_traceparent=model.mockau_traceparent,
            mockau_trace_id=model.mockau_trace_id,
            timestamp=model.timestamp,
            action_id=str(model.action_id),
        )

    def to_model(self) -> HttpRequestActionEventModel:
        return HttpRequestActionEventModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            action_id=self.action_id,
        )
