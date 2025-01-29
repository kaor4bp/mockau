from copy import deepcopy
from uuid import uuid4

from pydantic import Field

from schemas import HttpRequest
from schemas.base_schema import BaseSchema
from schemas.http_request.http_parts import HttpMethod
from schemas.http_request_override.http_parts import (
    HttpRequestOverrideHeaders,
    HttpRequestOverrideQueryParam,
    HttpRequestOverrideSocketAddress,
    t_HttpRequestOverrideContent,
)


class HttpRequestOverride(BaseSchema):
    path: str | None = None
    query_params: list[HttpRequestOverrideQueryParam] | None = None
    socket_address: HttpRequestOverrideSocketAddress | None = None
    method: HttpMethod | None = None
    headers: HttpRequestOverrideHeaders | None = None
    body: t_HttpRequestOverrideContent | None = Field(default=None, discriminator='type_of')

    def override_request(self, original_request: HttpRequest) -> HttpRequest:
        headers = deepcopy(self.headers or original_request.headers)
        new_id = uuid4()
        setattr(headers, 'x-mockau-request-id', [str(new_id)])
        return HttpRequest(
            id=new_id,
            socket_address=self.socket_address or original_request.socket_address,
            path=self.path or original_request.path,
            query_params=self.query_params if self.query_params is not None else original_request.query_params,
            method=self.method or original_request.method,
            headers=headers,
            body=self.body or original_request.body,
        )
