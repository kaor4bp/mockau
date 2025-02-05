from core.http.events.models.base_http_event_model import BaseHttpEventModel
from core.http.interaction.schemas import HttpRequest


class HttpRequestEventModel(BaseHttpEventModel):
    parent_mockau_traceparent: str | None = None
    http_request: HttpRequest
