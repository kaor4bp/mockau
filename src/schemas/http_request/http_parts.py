import base64
import gzip
import json
from enum import Enum
from typing import Literal, Optional
from urllib.parse import unquote

import httpx
import lxml.etree
from pydantic import ConfigDict, computed_field

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
    raw: str | None

    def to_binary(self):
        if self.raw:
            return gzip.decompress(base64.b64decode(self.raw.encode('utf8')))
        else:
            return None


class HttpRequestBinaryContent(HttpRequestContent):
    type_of: Literal['BINARY'] = 'BINARY'


class HttpRequestJsonContent(HttpRequestContent):
    type_of: Literal['JSON'] = 'JSON'
    encoding: str

    @classmethod
    def create_from_json(cls, json_data: dict | list) -> 'HttpRequestJsonContent':
        return cls(
            raw=base64.b64encode(gzip.compress(json.dumps(json_data, indent=2).encode('utf8'))).decode('utf8'),
            encoding='utf8',
        )

    @computed_field
    @property
    def json(self) -> dict | list:
        return json.loads(self.to_binary().decode(self.encoding))


class HttpRequestXmlContent(HttpRequestContent):
    type_of: Literal['XML'] = 'XML'
    encoding: str

    @computed_field
    @property
    def data(self) -> str:
        return self.to_binary().decode(self.encoding)


class HttpRequestTextContent(HttpRequestContent):
    type_of: Literal['TEXT'] = 'TEXT'
    encoding: str

    @computed_field
    @property
    def data(self) -> str:
        return self.to_binary().decode(self.encoding)


class HttpRequestNoContent(HttpRequestContent):
    type_of: Literal['NO_CONTENT'] = 'NO_CONTENT'

    # def to_binary(self):
    #     return None


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

    if content:
        raw_content = base64.b64encode(gzip.compress(content)).decode('utf8')
    else:
        raw_content = None

    try:
        text = content.decode(encoding)
    except UnicodeDecodeError:
        pass

    if text:
        if 'application/json' in content_type:
            try:
                json.loads(text)
            except json.JSONDecodeError:
                pass
            else:
                serialized_content = HttpRequestJsonContent(
                    raw=raw_content,
                    encoding=encoding,
                )
        elif 'xml' in content_type:
            try:
                lxml.etree.fromstring(text)
            except lxml.etree.XMLSyntaxError:
                pass
            else:
                serialized_content = HttpRequestXmlContent(encoding=encoding, raw=raw_content)
        else:
            serialized_content = HttpRequestTextContent(encoding=encoding, raw=raw_content)
    elif content:
        serialized_content = HttpRequestBinaryContent(
            raw=raw_content,
        )
    else:
        serialized_content = HttpRequestNoContent(raw=raw_content)

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
