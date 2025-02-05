from typing import Optional

from core.http.events.models.base_http_event_model import BaseHttpEventModel
from core.http.interaction.schemas import HttpRequest, HttpResponse


class HttpRequestResponseViewEventModel(BaseHttpEventModel):
    http_request: HttpRequest
    http_response: Optional[HttpResponse] = None
