import json
from typing import Optional

from elasticsearch_dsl import Keyword, Object, Text

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.events.inner_documents.http_header_inner_document import HttpHeaderInnerDocument
from core.http.interaction.schemas import HttpHeaders, HttpRequest


class HttpRequestInnerDocument(BaseModelInnerDocument):
    query_params: list[dict] = Object(multi=True, enabled=False)
    socket_address: dict = Object(enabled=False)
    headers: list[HttpHeaderInnerDocument] = Object(
        doc_class=HttpHeaderInnerDocument, multi=True, enabled=False, required=True
    )
    body: str = Keyword(required=True, store=True)

    url: str = Text(required=True)
    path: str = Keyword(required=True)
    method: str = Keyword(required=True)
    mockau_traceparent: str = Keyword(required=True)
    http_version: str = Keyword(required=True)
    text: Optional[str] = Keyword(required=False, store=True)

    @classmethod
    def from_model(cls, model: HttpRequest) -> 'HttpRequestInnerDocument':
        data = model.model_dump(mode='json')
        return cls(
            query_params=data['query_params'],
            socket_address=data.get('socket_address'),
            headers=HttpHeaderInnerDocument.from_model(model.headers),
            body=json.dumps(data['body']),
            url=str(model.get_full_url()),
            path=model.path,
            method=model.method.value,
            mockau_traceparent=model.mockau_traceparent,
            text=model.body.text,
            http_version=model.http_version,
        )

    def to_model(self) -> HttpRequest:
        data = self.to_dict()
        headers = HttpHeaders()
        for header in self.headers:
            setattr(headers, header.key, header.values)
        return HttpRequest(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=headers,
            method=data['method'],
            http_version=data['http_version'],
            body=json.loads(data['body']),
            mockau_traceparent=data['mockau_traceparent'],
        )
