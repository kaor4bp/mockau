from elasticsearch_dsl import Keyword, Object, Text

from core.bases.base_model_inner_document import BaseModelInnerDocument
from core.http.interaction.schemas import HttpHeaders, HttpRequest


class HttpRequestInnerDocument(BaseModelInnerDocument):
    query_params = Object(multi=True, enabled=False)
    socket_address = Object(enabled=False)
    headers = Object(enabled=False)
    body = Object(enabled=False)

    url = Text(required=True)
    path = Keyword(required=True)
    method = Text(required=True)
    mockau_traceparent = Text(required=True)
    http_version = Keyword(required=True)
    text = Keyword(required=False)

    @classmethod
    def from_model(cls, model: HttpRequest) -> 'HttpRequestInnerDocument':
        data = model.model_dump(mode='json')
        return cls(
            query_params=data['query_params'],
            socket_address=data.get('socket_address'),
            headers=data['headers'],
            body=data['body'],
            url=str(model.get_full_url()),
            path=model.path,
            method=model.method.value,
            mockau_traceparent=model.mockau_traceparent,
            text=model.body.text,
            http_version=model.http_version,
        )

    def to_model(self) -> HttpRequest:
        data = self.to_dict()
        return HttpRequest(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=data.get('headers', HttpHeaders()),
            method=data['method'],
            http_version=data['http_version'],
            body=data['body'],
            mockau_traceparent=data['mockau_traceparent'],
        )
