from typing import Optional

from elasticsearch_dsl import Float, Integer, Keyword, Object, Text

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.interaction.schemas import HttpCookies, HttpHeaders, HttpResponse


class HttpResponseInnerDocument(BaseModelInnerDocument):
    query_params: list[dict] = Object(multi=True, enabled=False, required=False)
    socket_address: Optional[dict] = Object(enabled=False, required=False)
    headers: dict = Object(enabled=False, required=True)
    content: dict = Object(enabled=False, required=True)
    cookies: Optional[dict] = Object(enabled=False, required=False)

    url: str = Text(required=True)
    path: str = Text(required=True)
    mockau_traceparent: Optional[str] = Keyword(required=False)
    text: str = Text(required=False)
    status_code: int = Integer(required=True)
    charset_encoding: Optional[str] = Keyword(required=False)
    elapsed: float = Float(required=True)
    encoding: Optional[str] = Keyword(required=False)
    http_version: str = Keyword(required=True)

    @classmethod
    def from_model(cls, model: HttpResponse) -> 'HttpResponseInnerDocument':
        data = model.model_dump(mode='json')
        return cls(
            query_params=data['query_params'],
            socket_address=data.get('socket_address'),
            headers=data['headers'],
            content=data['content'],
            cookies=data['cookies'],
            url=str(model.get_full_url()),
            path=model.path,
            mockau_traceparent=model.mockau_traceparent,
            text=model.content.text,
            status_code=model.status_code,
            http_version=model.http_version,
            charset_encoding=model.charset_encoding,
            encoding=model.encoding,
            elapsed=model.elapsed,
        )

    def to_model(self) -> HttpResponse:
        data = self.to_dict()
        return HttpResponse(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=data.get('headers', HttpHeaders()),
            status_code=data['status_code'],
            charset_encoding=data.get('charset_encoding'),
            elapsed=data['elapsed'],
            encoding=data.get('encoding'),
            content=data['content'],
            cookies=data.get('cookies', HttpCookies()),
        )
