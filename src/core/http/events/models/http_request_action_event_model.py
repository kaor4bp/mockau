from uuid import UUID

from core.http.events.models.base_http_event_model import BaseHttpEventModel


class HttpRequestActionEventModel(BaseHttpEventModel):
    action_id: UUID
