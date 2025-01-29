from uuid import UUID, uuid4

import httpx
from fastapi import Request
from pydantic import Field

from schemas.base_schema import BaseSchema
from schemas.http_request.http_parts import (
    HttpMethod,
    HttpRequestHeaders,
    HttpRequestQueryParam,
    HttpRequestSocketAddress,
    generate_http_content,
    t_Content,
)
from schemas.http_response import HttpResponse


class HttpRequest(BaseSchema):
    id: UUID = Field(default_factory=uuid4)

    path: str
    query_params: list[HttpRequestQueryParam]
    socket_address: HttpRequestSocketAddress | None
    method: HttpMethod
    headers: HttpRequestHeaders
    body: t_Content = Field(discriminator='type_of')

    def get_track_request_id(self) -> UUID | None:
        track_request_id = getattr(self.headers, 'x-mockau-request-id', None)
        if track_request_id:
            return UUID(track_request_id[0])

    @classmethod
    def from_httpx_request(cls, request: httpx.Request) -> 'HttpRequest':
        return cls(
            socket_address=HttpRequestSocketAddress.from_httpx_url(request.url),
            path=request.url.path,
            query_params=HttpRequestQueryParam.from_httpx_url(request.url),
            method=request.method.upper(),
            headers=HttpRequestHeaders.from_httpx_headers(request.headers),
            body=generate_http_content(
                content=request.content,
                content_type=request.headers.get('content-type', ''),
            ),
        )

    @classmethod
    async def from_fastapi_request(cls, request: Request) -> 'HttpRequest':
        httpx_url = httpx.URL(str(request.url))
        return cls(
            socket_address=HttpRequestSocketAddress.from_httpx_url(httpx_url),
            path=httpx_url.path,
            query_params=HttpRequestQueryParam.from_httpx_url(httpx_url),
            method=request.method.upper(),
            headers=HttpRequestHeaders.from_httpx_headers(request.headers),
            body=generate_http_content(
                content=await request.body(),
                content_type=request.headers.get('content-type', ''),
            ),
        )

    async def send(self) -> HttpResponse:
        client = httpx.AsyncClient()
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
        headers = []
        for header_name, header_values in self.headers:
            for header_value in header_values:
                headers.append((header_name, header_value))
        httpx_request = httpx.Request(
            method=self.method.value,
            url=url,
            headers=headers,
        )
        http_response = await client.send(httpx_request)
        return HttpResponse.from_httpx_response(http_response)
