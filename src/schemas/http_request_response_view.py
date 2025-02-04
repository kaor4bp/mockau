from schemas import BaseSchema, HttpRequest
from schemas.http_response import HttpResponse


class HttpRequestResponseView(BaseSchema):
    http_request: HttpRequest
    http_response: HttpResponse | None
    timestamp: int
