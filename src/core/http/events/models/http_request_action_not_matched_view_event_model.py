from uuid import UUID

from core.http.events.models.base_http_event_model import BaseHttpEventModel


class HttpRequestActionNotMatchedViewEventModel(BaseHttpEventModel):
    action_id: UUID
    action_revision: UUID
    description: str
