from urllib.parse import unquote

import httpx

from core.bases.base_schema import BaseSchema


class HttpQueryParam(BaseSchema):
    key: str
    value: str

    @classmethod
    def from_httpx_url(cls, url: httpx.URL) -> list['HttpQueryParam']:
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
