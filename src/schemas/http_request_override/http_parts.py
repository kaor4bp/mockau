from typing import Optional

from pydantic import Field

from core.bases.base_schema import BaseSchema
from core.http.interaction.schemas import (
    HttpBinaryContent,
    HttpContentEmpty,
    HttpCookies,
    HttpHeaders,
    HttpJsonContent,
    HttpQueryParam,
    HttpSocketAddress,
    HttpTextContent,
    HttpXmlContent,
)
from schemas.undefined_schema import UndefinedSchema


class HttpRequestOverrideCookies(HttpCookies):
    pass


class HttpRequestOverrideHeaders(HttpHeaders):
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


t_HttpRequestOverrideContent = HttpBinaryContent | HttpJsonContent | HttpXmlContent | HttpTextContent | HttpContentEmpty


class HttpRequestOverrideSocketAddress(HttpSocketAddress):
    host: Optional[str] = None
    port: Optional[int] | UndefinedSchema = Field(default_factory=UndefinedSchema)
    scheme: Optional[str] = None

    def override_http_socket_address(
        self,
        original_socket_address: HttpSocketAddress,
    ) -> HttpSocketAddress:
        return HttpSocketAddress(
            host=self.host if self.host else original_socket_address.host,
            port=original_socket_address.port if self.port == UndefinedSchema() else self.port,
            scheme=self.scheme if self.scheme else original_socket_address.scheme,
        )


class HttpRequestOverrideQueryParam(HttpQueryParam):
    key: str
    value: str
