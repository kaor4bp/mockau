import base64
import gzip
import json
import pathlib
from typing import Literal
from uuid import uuid4

import lxml.etree
from lxml import etree

from core.bases.base_schema import BaseSchema
from core.http.interaction.common import HttpContentType
from settings import MockauSettings


class BaseHttpContent(BaseSchema):
    type_of: HttpContentType
    file_id: str | None = None
    raw: str | None = None

    @property
    def text(self) -> str | None:
        return 'binary'

    @property
    def preview(self) -> str | None:
        return 'binary'

    def to_binary(self):
        if self.raw:
            return gzip.decompress(base64.b64decode(self.raw))
        elif self.file_id:
            with open(pathlib.Path(MockauSettings.path.content).joinpath(f'./{self.file_id}.dat'), 'rb') as f:
                return f.read()
        else:
            return b''


class HttpBinaryContent(BaseHttpContent):
    type_of: Literal['BINARY'] = 'BINARY'


class HttpJsonContent(BaseHttpContent):
    type_of: Literal['JSON'] = 'JSON'
    encoding: str

    @property
    def preview(self) -> str | None:
        text = self.text
        if len(text) > 100:
            return text[:100] + '...'
        else:
            return text

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)

    @classmethod
    def create_from_json(cls, json_data: dict | list) -> 'HttpJsonContent':
        return cls(
            raw=base64.b64encode(gzip.compress(json.dumps(json_data, indent=2).encode('utf8'))).decode('utf8'),
            encoding='utf8',
        )


class HttpXmlContent(BaseHttpContent):
    type_of: Literal['XML'] = 'XML'
    encoding: str

    @property
    def preview(self) -> str | None:
        text = self.text
        if len(text) > 100:
            return text[:100] + '...'
        else:
            return text

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)


class HttpTextContent(BaseHttpContent):
    type_of: Literal['TEXT'] = 'TEXT'
    encoding: str

    @property
    def preview(self) -> str | None:
        text = self.text
        if len(text) > 100:
            return text[:100] + '...'
        else:
            return text

    @property
    def text(self) -> str | None:
        return self.to_binary().decode(self.encoding)


class HttpContentEmpty(BaseHttpContent):
    type_of: Literal['EMPTY'] = 'EMPTY'

    @property
    def preview(self) -> str | None:
        text = self.text
        if text and len(text) > 100:
            return text[:100] + '...'
        else:
            return text

    @property
    def text(self) -> str | None:
        return None


HttpContent = HttpBinaryContent | HttpJsonContent | HttpXmlContent | HttpTextContent | HttpContentEmpty


def generate_http_content(content: bytes | None, content_type: str | None, encoding: str = 'utf8') -> HttpContent:
    serialized_content = None
    text = None
    content_type = content_type or ''

    if content:
        file_id = str(uuid4())
        file_path = pathlib.Path(MockauSettings.path.content).joinpath(f'./{file_id}.dat')
        with open(file_path, 'wb') as f:
            f.write(content or b'')
    else:
        file_id = None

    # if content:
    #     raw_content = base64.b64encode(gzip.compress(content)).decode('utf8')
    # else:
    #     raw_content = None

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
                serialized_content = HttpJsonContent(
                    file_id=file_id,
                    encoding=encoding,
                )
        elif 'xml' in content_type:
            try:
                parser = etree.XMLParser(encoding=encoding)
                lxml.etree.fromstring(content, parser=parser)
            except lxml.etree.LxmlError:
                pass
            else:
                serialized_content = HttpXmlContent(encoding=encoding, file_id=file_id)

        if not serialized_content:
            serialized_content = HttpTextContent(encoding=encoding, file_id=file_id)
    elif content:
        serialized_content = HttpBinaryContent(file_id=file_id)
    else:
        serialized_content = HttpContentEmpty(file_id=file_id)

    return serialized_content
