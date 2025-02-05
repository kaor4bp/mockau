import httpx
from pydantic import ConfigDict

from core.bases.base_schema import BaseSchema


class HttpCookies(BaseSchema):
    model_config = ConfigDict(
        extra='allow',
        json_schema_extra={
            'additionalProperties': {
                'type': 'string',
            }
        },
    )

    @classmethod
    def from_httpx_cookies(cls, cookies: httpx.Cookies) -> 'HttpCookies':
        return cls(**dict(cookies.items()))
