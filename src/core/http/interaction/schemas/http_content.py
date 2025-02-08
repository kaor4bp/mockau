import base64
import gzip
import json
from typing import Literal

import lxml.etree
from lxml import etree
from pydantic import computed_field

from core.bases.base_schema import BaseSchema
from core.http.interaction.common import HttpContentType


class BaseHttpContent(BaseSchema):
    type_of: HttpContentType
    raw: str | None = None

    @property
    def text(self) -> str | None:
        return 'binary'

    def to_binary(self):
        if self.raw:
            return gzip.decompress(base64.b64decode(self.raw.encode('utf8')))
        else:
            return None


class HttpBinaryContent(BaseHttpContent):
    type_of: Literal['BINARY'] = 'BINARY'


class HttpJsonContent(BaseHttpContent):
    type_of: Literal['JSON'] = 'JSON'
    encoding: str

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)

    @classmethod
    def create_from_json(cls, json_data: dict | list) -> 'HttpJsonContent':
        return cls(
            raw=base64.b64encode(gzip.compress(json.dumps(json_data, indent=2).encode('utf8'))).decode('utf8'),
            encoding='utf8',
        )

    @computed_field
    @property
    def json(self) -> dict | list:
        return json.loads(self.to_binary().decode(self.encoding))


class HttpXmlContent(BaseHttpContent):
    type_of: Literal['XML'] = 'XML'
    encoding: str

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)


class HttpTextContent(BaseHttpContent):
    type_of: Literal['TEXT'] = 'TEXT'
    encoding: str

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)


class HttpContentEmpty(BaseHttpContent):
    type_of: Literal['EMPTY'] = 'EMPTY'

    @property
    def text(self) -> str | None:
        return None


HttpContent = HttpBinaryContent | HttpJsonContent | HttpXmlContent | HttpTextContent | HttpContentEmpty


def generate_http_content(content: bytes | None, content_type: str | None, encoding: str | None = None) -> HttpContent:
    serialized_content = None
    text = None
    content_type = content_type or ''

    if content:
        raw_content = base64.b64encode(gzip.compress(content)).decode('utf8')
    else:
        raw_content = None

    try:
        text = content.decode(encoding or 'utf8')
    except UnicodeDecodeError:
        pass

    if text:
        if 'application/json' in content_type:
            try:
                json.loads(text)
            except json.JSONDecodeError:
                pass
            else:
                serialized_content = HttpJsonContent(
                    raw=raw_content,
                    encoding=encoding,
                )
        elif 'xml' in content_type:
            try:
                parser = etree.XMLParser(encoding=encoding or 'utf8')
                lxml.etree.fromstring(raw_content, parser=parser)
            except lxml.etree.LxmlError:
                pass
            else:
                serialized_content = HttpXmlContent(encoding=encoding, raw=raw_content)

        if not serialized_content:
            serialized_content = HttpTextContent(encoding=encoding, raw=raw_content)
    elif content:
        serialized_content = HttpBinaryContent(
            raw=raw_content,
        )
    else:
        serialized_content = HttpContentEmpty(raw=raw_content)

    return serialized_content
