from typing import Optional

from schemas.http_request.http_parts import (
    HttpRequestBinaryContent,
    HttpRequestCookies,
    HttpRequestHeaders,
    HttpRequestJsonContent,
    HttpRequestNoContent,
    HttpRequestQueryParam,
    HttpRequestSocketAddress,
    HttpRequestTextContent,
    HttpRequestXmlContent,
)


class HttpRequestModifyCookies(HttpRequestCookies):
    pass


class HttpRequestModifyHeaders(HttpRequestHeaders):
    pass


class HttpRequestModifyBinaryContent(HttpRequestBinaryContent):
    data: str


class HttpRequestModifyJsonContent(HttpRequestJsonContent):
    data: list | dict


class HttpRequestModifyXmlContent(HttpRequestXmlContent):
    data: str


class HttpRequestModifyTextContent(HttpRequestTextContent):
    data: str


class HttpRequestModifyNoContent(HttpRequestNoContent):
    data: None = None


t_HttpRequestModifyContent = (
    HttpRequestBinaryContent
    | HttpRequestJsonContent
    | HttpRequestXmlContent
    | HttpRequestTextContent
    | HttpRequestNoContent
)


class HttpRequestModifySocketAddress(HttpRequestSocketAddress):
    host: Optional[str] = None
    port: Optional[int] = None
    scheme: Optional[str] = None


class HttpRequestModifyQueryParam(HttpRequestQueryParam):
    key: str
    value: str
