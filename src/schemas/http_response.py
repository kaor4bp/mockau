import httpx
from fastapi import Response
from pydantic import Field

from schemas.http_request.http_parts import (
    HttpRequestCookies,
    HttpRequestHeaders,
    HttpRequestQueryParam,
    HttpRequestSocketAddress,
    generate_http_content,
    t_Content,
)

from .base_schema import BaseSchema


class HttpResponse(BaseSchema):
    path: str
    query_params: list[HttpRequestQueryParam]
    host: HttpRequestSocketAddress | None
    headers: HttpRequestHeaders
    status_code: int
    charset_encoding: str | None
    elapsed: float
    encoding: str | None
    content: t_Content = Field(discriminator='type_of')
    cookies: HttpRequestCookies
    http_version: str = 'HTTP/1.1'

    @property
    def has_redirect_location(self) -> bool:
        return bool(getattr(self.headers, 'location', None))

    @classmethod
    def from_httpx_response(cls, response: httpx.Response) -> 'HttpResponse':
        return cls(
            host=HttpRequestSocketAddress.from_httpx_url(response.url),
            path=response.url.path,
            query_params=HttpRequestQueryParam.from_httpx_url(response.url),
            headers=HttpRequestHeaders.from_httpx_headers(response.headers),
            status_code=response.status_code,
            charset_encoding=response.charset_encoding,
            elapsed=response.elapsed.total_seconds(),
            encoding=response.encoding,
            content=generate_http_content(
                content=response.content,
                content_type=response.headers.get('content-type', ''),
                encoding=response.encoding,
            ),
            cookies=HttpRequestCookies.from_httpx_cookies(response.cookies),
            http_version=response.http_version,
        )

    def to_fastapi_response(self) -> Response:
        headers = {}
        for header_name, header_values in self.headers.model_dump(mode='json').items():
            for header_value in header_values:
                headers[header_name] = header_value

        return Response(
            content=self.content.to_binary(),
            status_code=self.status_code,
            headers=headers,
        )
