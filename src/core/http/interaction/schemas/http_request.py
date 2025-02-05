from copy import deepcopy
from uuid import UUID

import httpx
from fastapi import Request
from pydantic import Field

from consts import X_MOCKAU_TRACEPARENT_HEADER
from core.bases.base_schema import BaseSchema
from core.http.interaction.common import HttpMethod
from core.http.interaction.schemas.http_content import generate_http_content
from core.http.interaction.schemas.http_headers import HttpHeaders
from core.http.interaction.schemas.http_query_param import HttpQueryParam
from core.http.interaction.schemas.http_response import HttpResponse
from core.http.interaction.schemas.http_socket_address import HttpSocketAddress
from core.http.interaction.types import t_Content
from utils.traceparent import generate_traceparent_token


class HttpRequest(BaseSchema):
    path: str
    query_params: list[HttpQueryParam]
    socket_address: HttpSocketAddress | None
    method: HttpMethod
    headers: HttpHeaders
    body: t_Content = Field(discriminator='type_of')
    http_version: str = 'HTTP/1.1'
    mockau_traceparent: str

    @property
    def mockau_trace_id(self) -> str:
        _, trace_id, _, _ = self.mockau_traceparent.split('-')
        return trace_id

    @property
    def is_external(self) -> bool:
        return not hasattr(self.headers, X_MOCKAU_TRACEPARENT_HEADER)

    def get_track_request_id(self) -> UUID | None:
        track_request_id = getattr(self.headers, 'x-mockau-request-id', None)
        if track_request_id:
            return UUID(track_request_id[0])

    @classmethod
    def from_httpx_request(cls, request: httpx.Request) -> 'HttpRequest':
        mockau_traceparent = request.headers.get(X_MOCKAU_TRACEPARENT_HEADER, generate_traceparent_token())

        return cls(
            socket_address=HttpSocketAddress.from_httpx_url(request.url),
            path=request.url.path,
            query_params=HttpQueryParam.from_httpx_url(request.url),
            method=request.method.upper(),
            headers=HttpHeaders.from_httpx_headers(request.headers),
            body=generate_http_content(
                content=request.content,
                content_type=request.headers.get('content-type', ''),
            ),
            mockau_traceparent=mockau_traceparent,
        )

    @classmethod
    async def from_fastapi_request(cls, request: Request) -> 'HttpRequest':
        mockau_traceparent = request.headers.get(X_MOCKAU_TRACEPARENT_HEADER, generate_traceparent_token())

        httpx_url = httpx.URL(str(request.url))
        return cls(
            socket_address=HttpSocketAddress.from_httpx_url(httpx_url),
            path=httpx_url.path,
            query_params=HttpQueryParam.from_httpx_url(httpx_url),
            method=request.method.upper(),
            headers=HttpHeaders.from_httpx_headers(request.headers),
            body=generate_http_content(
                content=await request.body(),
                content_type=request.headers.get('content-type', ''),
            ),
            mockau_traceparent=mockau_traceparent,
        )

    def get_full_url(self) -> httpx.URL:
        url = httpx.URL(self.path)
        if self.socket_address:
            url = url.copy_with(
                host=self.socket_address.host,
                scheme=self.socket_address.scheme,
            )
        if self.socket_address and self.socket_address.port is not None:
            url = url.copy_with(port=self.socket_address.port)
        if self.query_params:
            url = url.copy_with(
                query='&'.join([f'{param.key}={param.value}' for param in self.query_params]).encode('utf8')
            )
        return url

    async def send(self, client: httpx.AsyncClient) -> HttpResponse:
        headers = []
        for header_name, header_values in self.headers:
            for header_value in header_values:
                headers.append((header_name, header_value))
        httpx_request = httpx.Request(
            method=self.method.value,
            url=self.get_full_url(),
            headers=headers,
        )
        http_response = await client.send(httpx_request)
        return HttpResponse.from_httpx_response(http_response)

    def follow_redirect(self, http_response: HttpResponse) -> 'HttpRequest':
        location = httpx.URL(getattr(http_response.headers, 'location')[0])
        http_request = deepcopy(self)

        mockau_traceparent_token = generate_traceparent_token(http_response.mockau_traceparent)
        setattr(http_request.headers, X_MOCKAU_TRACEPARENT_HEADER, [mockau_traceparent_token])

        http_request.socket_address = HttpSocketAddress.from_httpx_url(location)
        http_request.path = location.path
        http_request.query_params = HttpQueryParam.from_httpx_url(location)

        return http_request
