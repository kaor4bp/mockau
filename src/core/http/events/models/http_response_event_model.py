from core.http.events.models.base_http_event_model import BaseHttpEventModel
from core.http.interaction.schemas.http_response import HttpResponse


class HttpResponseEventModel(BaseHttpEventModel):
    http_response: HttpResponse
