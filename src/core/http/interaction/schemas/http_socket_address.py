from typing import Optional

import httpx

from core.bases.base_schema import BaseSchema


class HttpSocketAddress(BaseSchema):
    host: str
    port: int | None = None
    scheme: str

    @classmethod
    def from_httpx_url(cls, url: httpx.URL) -> Optional['HttpSocketAddress']:
        if url.is_absolute_url:
            return cls(
                host=url.host,
                port=url.port,
                scheme=url.scheme,
            )
