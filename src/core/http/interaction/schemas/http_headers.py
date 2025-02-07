import httpx
from pydantic import ConfigDict

from core.bases.base_schema import BaseSchema


class HttpHeaders(BaseSchema):
    model_config = ConfigDict(
        extra='allow', json_schema_extra={'additionalProperties': {'type': 'array', 'items': {'type': 'string'}}}
    )

    @classmethod
    def from_httpx_headers(cls, headers: httpx.Headers) -> 'HttpHeaders':
        mapped_headers = {}
        for header_name, header_value in headers.raw:
            header_name = header_name.decode("utf-8")
            header_value = header_value.decode("utf-8")
            mapped_headers.setdefault(header_name, []).append(header_value)

        return cls(**mapped_headers)

    @classmethod
    def from_fastapi_headers(cls, request) -> 'HttpHeaders':
        mapped_headers = {}
        for header_name, header_value in request.scope["headers"]:
            header_name = header_name.decode("utf-8")
            header_value = header_value.decode("utf-8")
            mapped_headers.setdefault(header_name, []).append(header_value)

        return cls(**mapped_headers)
