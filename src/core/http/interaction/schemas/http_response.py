from urllib.parse import urlencode

import httpx
from fastapi import Response
from pydantic import Field

from core.bases.base_schema import BaseSchema
from core.http.interaction.consts import X_MOCKAU_TRACEPARENT_HEADER
from core.http.interaction.schemas.http_content import generate_http_content
from core.http.interaction.schemas.http_cookies import HttpCookies
from core.http.interaction.schemas.http_headers import HttpHeaders
from core.http.interaction.schemas.http_query_param import HttpQueryParam
from core.http.interaction.schemas.http_socket_address import HttpSocketAddress
from core.http.interaction.types import t_Content


class HttpResponse(BaseSchema):
    path: str
    query_params: list[HttpQueryParam]
    socket_address: HttpSocketAddress | None = None
    headers: HttpHeaders
    status_code: int
    charset_encoding: str | None = None
    elapsed: float
    encoding: str | None = None
    content: t_Content = Field(discriminator='type_of')
    cookies: HttpCookies
    http_version: str = 'HTTP/1.1'

    @property
    def mockau_traceparent(self) -> str | None:
        return getattr(self.headers, X_MOCKAU_TRACEPARENT_HEADER, None)

    @property
    def full_url(self) -> httpx.URL:
        url = httpx.URL(self.path)
        if self.socket_address:
            url = url.copy_with(
                host=self.socket_address.host,
                scheme=self.socket_address.scheme,
            )
        if self.socket_address and self.socket_address.port is not None:
            url = url.copy_with(port=self.socket_address.port)
        if self.query_params:
            url = url.copy_with(params=urlencode([(param.key, param.value) for param in self.query_params]))
        return url

    @property
    def has_redirect_location(self) -> bool:
        return bool(getattr(self.headers, 'location', None))

    @classmethod
    async def from_httpx_response(
        cls,
        response: httpx.Response,
        request,
    ) -> 'HttpResponse':
        original_content_encoding = response.headers.get('content-encoding')
        response.headers.update({'content-encoding': 'identity'})
        content = await response.aread()
        if original_content_encoding:
            response.headers.update({'content-encoding': original_content_encoding})
        await response.aclose()

        result = cls(
            socket_address=HttpSocketAddress.from_httpx_url(response.url),
            path=response.url.path,
            query_params=HttpQueryParam.from_httpx_url(response.url),
            headers=HttpHeaders.from_httpx_headers(response.headers),
            status_code=response.status_code,
            charset_encoding=response.charset_encoding,
            elapsed=response.elapsed.total_seconds(),
            encoding=response.encoding,
            content=generate_http_content(
                content=content,
                content_type=response.headers.get('content-type', ''),
                encoding=response.encoding,
            ),
            cookies=HttpCookies.from_httpx_cookies(response.cookies),
            http_version=response.http_version,
        )
        result.headers.adopt_cookies(request, result)

        return result

    def to_fastapi_response(self) -> Response:
        headers = {}
        for header_name, header_values in self.headers.model_dump(mode='json').items():
            for header_value in header_values:
                headers[header_name] = header_value

        return Response(
            content=self.content.to_raw_binary(),
            status_code=self.status_code,
            headers=headers,
        )
