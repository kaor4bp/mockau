import base64
import json
from abc import abstractmethod
from enum import Enum
from typing import Literal, Optional
from urllib.parse import unquote

import httpx
import lxml.etree
from pydantic import ConfigDict

from consts import FORBIDDEN_HEADERS
from schemas.base_schema import BaseSchema


class HttpRequestCookies(BaseSchema):
    model_config = ConfigDict(
        extra='allow',
        json_schema_extra={
            'additionalProperties': {
                'type': 'string',
            }
        },
    )

    @classmethod
    def from_httpx_cookies(cls, cookies: httpx.Cookies) -> 'HttpRequestCookies':
        return cls(**dict(cookies.items()))


class HttpRequestHeaders(BaseSchema):
    model_config = ConfigDict(
        extra='allow', json_schema_extra={'additionalProperties': {'type': 'array', 'items': {'type': 'string'}}}
    )

    @classmethod
    def from_httpx_headers(cls, headers: httpx.Headers) -> 'HttpRequestHeaders':
        mapped_headers = {}
        for header_name, header_value in headers.items():
            if header_name.lower() in FORBIDDEN_HEADERS:
                continue
            mapped_headers.setdefault(header_name, []).append(header_value)

        return cls(**mapped_headers)


class HttpMethod(Enum):
    GET = 'GET'
    POST = 'POST'
    PUT = 'PUT'
    DELETE = 'DELETE'
    PATCH = 'PATCH'
    HEAD = 'HEAD'
    OPTIONS = 'OPTIONS'
    TRACE = 'TRACE'


class HttpContentType(Enum):
    BINARY = 'BINARY'
    XML = 'XML'
    JSON = 'JSON'
    TEXT = 'TEXT'
    NO_CONTENT = 'NO_CONTENT'


class HttpRequestContent(BaseSchema):
    type_of: HttpContentType
    content_type: str

    @abstractmethod
    def to_binary(self) -> bytes:
        pass


class HttpRequestBinaryContent(HttpRequestContent):
    type_of: Literal['BINARY'] = 'BINARY'
    data: str

    def to_binary(self):
        return base64.b64encode(self.data.encode('utf8'))


class HttpRequestJsonContent(HttpRequestContent):
    type_of: Literal['JSON'] = 'JSON'
    data: list | dict
    encoding: str

    def to_binary(self):
        return json.dumps(self.data).encode(self.encoding)


class HttpRequestXmlContent(HttpRequestContent):
    type_of: Literal['XML'] = 'XML'
    data: str
    encoding: str

    def to_binary(self):
        return self.data.encode(self.encoding)


class HttpRequestTextContent(HttpRequestContent):
    type_of: Literal['TEXT'] = 'TEXT'
    data: str
    encoding: str

    def to_binary(self):
        return self.data.encode(self.encoding)


class HttpRequestNoContent(HttpRequestContent):
    type_of: Literal['NO_CONTENT'] = 'NO_CONTENT'
    data: None = None

    def to_binary(self):
        return None


t_Content = (
    HttpRequestBinaryContent
    | HttpRequestJsonContent
    | HttpRequestXmlContent
    | HttpRequestTextContent
    | HttpRequestNoContent
)


def generate_http_content(content: bytes | None, content_type: str | None, encoding: str = 'utf-8') -> t_Content:
    serialized_content = None
    text = None
    content_type = content_type or ''
    try:
        text = content.decode(encoding)
    except UnicodeDecodeError:
        pass

    if text:
        if 'application/json' in content_type:
            try:
                serialized_content = HttpRequestJsonContent(
                    data=json.loads(text), encoding=encoding, content_type=content_type
                )
            except json.JSONDecodeError:
                pass
        elif 'xml' in content_type:
            try:
                lxml.etree.fromstring(text)
            except lxml.etree.XMLSyntaxError:
                pass
            else:
                serialized_content = HttpRequestXmlContent(data=text, encoding=encoding, content_type=content_type)
        else:
            serialized_content = HttpRequestTextContent(data=text, encoding=encoding, content_type=content_type)
    elif content:
        serialized_content = HttpRequestBinaryContent(
            data=base64.b64encode(content).decode('utf8'), content_type=content_type
        )
    else:
        serialized_content = HttpRequestNoContent(content_type=content_type)

    return serialized_content


class HttpRequestSocketAddress(BaseSchema):
    host: str
    port: int | None = None
    scheme: str

    @classmethod
    def from_httpx_url(cls, url: httpx.URL) -> Optional['HttpRequestSocketAddress']:
        if url.is_absolute_url:
            return cls(
                host=url.host,
                port=url.port,
                scheme=url.scheme,
            )


class HttpRequestQueryParam(BaseSchema):
    key: str
    value: str

    @classmethod
    def from_httpx_url(cls, url: httpx.URL) -> list['HttpRequestQueryParam']:
        decoded_query = url.query.decode('utf8')
        if not decoded_query:
            return []

        raw_params = decoded_query.split('&')
        params = []
        for raw_param in raw_params:
            values = raw_param.split('=')
            if len(values) == 1:
                key = unquote(values[0])
                value = ''
            else:
                key, value = values
                key, value = unquote(key), unquote(value)
            params.append(cls(key=key, value=value))
        return params
