import httpx
from pydantic import ConfigDict

from core.bases.base_schema import BaseSchema
from core.http.interaction.schemas import HttpRequest, HttpResponse


class HttpHeaders(BaseSchema):
    model_config = ConfigDict(
        extra='allow', json_schema_extra={'additionalProperties': {'type': 'array', 'items': {'type': 'string'}}}
    )

    @property
    def as_mapping(self) -> dict[str, str]:
        return self.model_dump(mode='json')

    def adopt_cookies(self, http_request: HttpRequest, http_response: HttpResponse) -> None:
        for header_name, header_values in self.as_mapping.items():
            if header_name.lower().startswith('set-cookie:'):
                new_set_cookie_header_values = []
                for header_value in header_values:
                    if http_request.socket_address.host != http_response.socket_address.host:
                        header_value = header_value.replace(
                            http_response.socket_address.host, http_request.socket_address.host
                        )
                    if http_request.socket_address.scheme == 'https' and ' Secure;' not in header_value:
                        header_value += ' Secure;'
                    if http_request.socket_address.scheme == 'http' and ' Secure;' in header_value:
                        header_value.replace(' Secure;', '')
                    new_set_cookie_header_values.append(header_value)
                setattr(self, header_name, new_set_cookie_header_values)

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
