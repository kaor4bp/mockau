import base64
import gzip
import json
import pathlib
import zlib
from typing import Literal
from uuid import uuid4

import brotli
import lxml.etree
from lxml import etree
from pydantic import computed_field

from core.bases.base_schema import BaseSchema
from core.http.interaction.common import HttpContentType
from settings import MockauSettings
from utils.compression import detect_and_decompress
from utils.formatters import format_bytes_size_to_human_readable


def get_data_file_path_by_id(file_id: str) -> pathlib.Path:
    return pathlib.Path(MockauSettings.path.content).joinpath(f'./{file_id}.dat').resolve()


class BaseHttpContent(BaseSchema):
    type_of: HttpContentType
    file_id: str | None = None
    raw: str | None = None
    compression: str | None = None

    @computed_field
    @property
    def size(self) -> str:
        if self.file_id:
            size = get_data_file_path_by_id(self.file_id).stat().st_size
        elif self.raw:
            size = len(gzip.decompress(base64.b64decode(self.raw)))
        else:
            size = 0
        return format_bytes_size_to_human_readable(size)

    @property
    def text(self) -> str | None:
        return 'binary'

    @property
    def preview(self) -> str | None:
        return 'binary'

    def to_raw_binary(self) -> bytes | None:
        if self.raw:
            return gzip.decompress(base64.b64decode(self.raw))
        elif self.file_id:
            with open(get_data_file_path_by_id(self.file_id), 'rb') as f:
                return f.read()

    def to_binary(self) -> bytes | None:
        if self.raw:
            return gzip.decompress(base64.b64decode(self.raw))
        elif self.file_id:
            with open(get_data_file_path_by_id(self.file_id), 'rb') as f:
                content = f.read()

            if self.compression is None:
                return content
            elif self.compression == 'gzip':
                return gzip.decompress(content)
            elif self.compression == 'zlib':
                return zlib.decompress(content)
            elif self.compression == 'brotli':
                return brotli.decompress(content)
            else:
                raise AttributeError(f'Unknown compression type "{self.compression}"')


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


def generate_http_content(
    content: bytes | None,
    content_type: str | None,
    encoding: str = 'utf8',
) -> HttpContent:
    serialized_content = None
    text = None
    content_type = content_type or ''

    if content:
        file_id = str(uuid4())
        with open(get_data_file_path_by_id(file_id), 'wb') as f:
            f.write(content)
    else:
        file_id = None

    compression, decompressed_content = detect_and_decompress(content)

    try:
        text = decompressed_content.decode(encoding)
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
                    compression=compression,
                )
        elif 'xml' in content_type:
            try:
                parser = etree.XMLParser(encoding=encoding)
                lxml.etree.fromstring(decompressed_content, parser=parser)
            except lxml.etree.LxmlError:
                pass
            else:
                serialized_content = HttpXmlContent(encoding=encoding, file_id=file_id, compression=compression)

        if not serialized_content:
            serialized_content = HttpTextContent(encoding=encoding, file_id=file_id, compression=compression)
    elif decompressed_content:
        serialized_content = HttpBinaryContent(file_id=file_id, compression=compression)
    else:
        serialized_content = HttpContentEmpty(file_id=file_id, compression=compression)

    return serialized_content
