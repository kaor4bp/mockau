from copy import deepcopy
from uuid import uuid4

from pydantic_core import PydanticUndefined

from schemas import HttpRequest
from schemas.base_schema import BaseSchema
from schemas.http_request.http_parts import HttpMethod, HttpRequestSocketAddress
from schemas.http_request.http_request import HttpRequestClientSettings
from schemas.http_request_override.http_parts import (
    HttpRequestOverrideHeaders,
    HttpRequestOverrideQueryParam,
    HttpRequestOverrideSocketAddress,
)


class HttpRequestOverride(BaseSchema):
    path: str | None = None
    query_params: list[HttpRequestOverrideQueryParam] | None = None
    socket_address: HttpRequestOverrideSocketAddress | None = None
    method: HttpMethod | None = None
    headers: HttpRequestOverrideHeaders | None = None

    client_settings: HttpRequestClientSettings | None = None

    # body: t_HttpRequestOverrideContent | None = Field(default=None, discriminator='type_of')

    def override_http_request(self, original_request: HttpRequest) -> HttpRequest:
        headers = deepcopy(self.headers or original_request.headers)
        new_id = uuid4()
        setattr(headers, 'x-mockau-request-id', [str(new_id)])

        return HttpRequest(
            id=new_id,
            socket_address=HttpRequestSocketAddress(
                host=(
                    self.socket_address.host
                    if self.socket_address and self.socket_address.host is not PydanticUndefined
                    else original_request.socket_address.host
                ),
                port=(
                    self.socket_address.port
                    if self.socket_address and self.socket_address.port is not PydanticUndefined
                    else original_request.socket_address.port
                ),
                scheme=(
                    self.socket_address.scheme
                    if self.socket_address and self.socket_address.scheme is not PydanticUndefined
                    else original_request.socket_address.scheme
                ),
            ),
            path=self.path or original_request.path,
            query_params=(self.query_params if self.query_params is not None else original_request.query_params),
            method=self.method or original_request.method,
            headers=headers,
            body=original_request.body,
            client_settings=self.client_settings or original_request.client_settings,
            # body=self.body or original_request.body,
        )
