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


class HttpRequestOverrideCookies(HttpRequestCookies):
    pass


class HttpRequestOverrideHeaders(HttpRequestHeaders):
    pass


class HttpRequestOverrideBinaryContent(HttpRequestBinaryContent):
    data: str


class HttpRequestOverrideJsonContent(HttpRequestJsonContent):
    data: list | dict


class HttpRequestOverrideXmlContent(HttpRequestXmlContent):
    data: str


class HttpRequestOverrideTextContent(HttpRequestTextContent):
    data: str


class HttpRequestOverrideNoContent(HttpRequestNoContent):
    data: None = None


t_HttpRequestOverrideContent = (
    HttpRequestBinaryContent
    | HttpRequestJsonContent
    | HttpRequestXmlContent
    | HttpRequestTextContent
    | HttpRequestNoContent
)


class HttpRequestOverrideSocketAddress(HttpRequestSocketAddress):
    host: Optional[str] = None
    port: Optional[int] = None
    scheme: Optional[str] = None


class HttpRequestOverrideQueryParam(HttpRequestQueryParam):
    key: str
    value: str
