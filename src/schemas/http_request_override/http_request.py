from copy import deepcopy

from pydantic_core import PydanticUndefined

from consts import X_MOCKAU_TRACEPARENT_HEADER
from schemas import HttpRequest
from schemas.base_schema import BaseSchema
from schemas.http_request.http_parts import HttpMethod, HttpRequestSocketAddress
from schemas.http_request_override.http_parts import (
    HttpRequestOverrideHeaders,
    HttpRequestOverrideQueryParam,
    HttpRequestOverrideSocketAddress,
)
from utils.traceparent import generate_traceparent_token


class HttpRequestOverride(BaseSchema):
    path: str | None = None
    query_params: list[HttpRequestOverrideQueryParam] | None = None
    socket_address: HttpRequestOverrideSocketAddress | None = None
    method: HttpMethod | None = None
    headers: HttpRequestOverrideHeaders | None = None

    # body: t_HttpRequestOverrideContent | None = Field(default=None, discriminator='type_of')

    def override_http_request(self, original_request: HttpRequest) -> HttpRequest:
        headers = deepcopy(self.headers or original_request.headers)
        mockau_traceparent_token = generate_traceparent_token(original_request.mockau_traceparent)
        setattr(headers, X_MOCKAU_TRACEPARENT_HEADER, [mockau_traceparent_token])

        return HttpRequest(
            mockau_traceparent=mockau_traceparent_token,
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
            # body=self.body or original_request.body,
        )
