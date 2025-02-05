from core.bases.base_schema import BaseSchema
from core.http.interaction.schemas import HttpRequest
from core.http.interaction.schemas.http_response import HttpResponse


class HttpRequestResponseView(BaseSchema):
    http_request: HttpRequest
    http_response: HttpResponse | None
    timestamp: int
