import json
from typing import Optional

from elasticsearch_dsl import Float, Integer, Keyword, Object, Text

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.events.inner_documents.http_header_inner_document import HttpHeaderInnerDocument
from core.http.interaction.schemas import HttpCookies, HttpHeaders, HttpResponse


class HttpResponseInnerDocument(BaseModelInnerDocument):
    query_params: list[dict] = Object(multi=True, enabled=False, required=False)
    socket_address: Optional[dict] = Object(enabled=False, required=False)
    headers: list[HttpHeaderInnerDocument] = Object(
        enabled=False, required=True, multi=True, doc_class=HttpHeaderInnerDocument
    )
    content: str = Keyword(required=True)
    cookies: Optional[dict] = Object(enabled=False, required=False)

    url: str = Text(required=True)
    path: str = Keyword(required=True)
    mockau_traceparent: Optional[str] = Keyword(required=False)
    text: Optional[str] = Keyword(required=False)
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
            headers=HttpHeaderInnerDocument.from_model(model.headers),
            content=json.dumps(data['content']),
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
        headers = HttpHeaders()
        for header in self.headers:
            setattr(headers, header.key, header.values)
        return HttpResponse(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=headers,
            status_code=data['status_code'],
            charset_encoding=data.get('charset_encoding'),
            elapsed=data['elapsed'],
            encoding=data.get('encoding'),
            content=json.loads(data['content']),
            cookies=data.get('cookies', HttpCookies()),
        )
