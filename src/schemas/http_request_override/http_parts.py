from typing import Optional

from pydantic import Field

from schemas import BaseSchema
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
from schemas.undefined_schema import UndefinedSchema


class HttpRequestOverrideCookies(HttpRequestCookies):
    pass


class HttpRequestOverrideHeaders(HttpRequestHeaders):
    pass


class HttpRequestOverrideBinaryContent(BaseSchema):
    data: str


class HttpRequestOverrideJsonContent(BaseSchema):
    data: list | dict


class HttpRequestOverrideXmlContent(BaseSchema):
    data: str


class HttpRequestOverrideTextContent(BaseSchema):
    data: str


class HttpRequestOverrideNoContent(BaseSchema):
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
    port: Optional[int] | UndefinedSchema = Field(default_factory=UndefinedSchema)
    scheme: Optional[str] = None

    def override_http_socket_address(
        self,
        original_socket_address: HttpRequestSocketAddress,
    ) -> HttpRequestSocketAddress:
        return HttpRequestSocketAddress(
            host=self.host if self.host else original_socket_address.host,
            port=original_socket_address.port if self.port == UndefinedSchema() else self.port,
            scheme=self.scheme if self.scheme else original_socket_address.scheme,
        )


class HttpRequestOverrideQueryParam(HttpRequestQueryParam):
    key: str
    value: str
