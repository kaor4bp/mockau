import asyncio

import pytz
from elasticsearch import AsyncElasticsearch
from elasticsearch_dsl import AsyncDocument, Date, Float, InnerDoc, Integer, Keyword, Long, Object, Text

from models.events import (
    EventHttpRequestActionModel,
    EventHttpRequestErrorModel,
    EventHttpRequestModel,
    EventHttpRequestResponseViewModel,
    EventHttpResponseModel,
)
from schemas import HttpRequest
from schemas.http_request.http_parts import HttpRequestCookies, HttpRequestHeaders
from schemas.http_response import HttpResponse
from settings import MockauSettings


class HttpRequestDocument(InnerDoc):
    query_params = Object(multi=True, enabled=False)
    socket_address = Object(enabled=False)
    headers = Object(enabled=False)
    body = Object(enabled=False)

    url = Text(required=True)
    path = Text(required=True)
    method = Keyword(required=True)
    mockau_traceparent = Keyword(required=True)
    http_version = Keyword(required=True)
    text = Text(required=False)

    @classmethod
    def from_http_request(cls, request: HttpRequest) -> 'HttpRequestDocument':
        data = request.model_dump(mode='json')
        return cls(
            query_params=data['query_params'],
            socket_address=data.get('socket_address'),
            headers=data['headers'],
            body=data['body'],
            url=str(request.get_full_url()),
            path=request.path,
            method=request.method.value,
            mockau_traceparent=request.mockau_traceparent,
            text=request.body.text,
            http_version=request.http_version,
        )

    def to_http_request(self) -> HttpRequest:
        data = self.to_dict()
        return HttpRequest(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=data.get('headers', HttpRequestHeaders()),
            method=data['method'],
            http_version=data['http_version'],
            body=data['body'],
            mockau_traceparent=data['mockau_traceparent'],
        )


class HttpResponseDocument(InnerDoc):
    query_params = Object(multi=True, enabled=False, required=False)
    socket_address = Object(enabled=False, required=False)
    headers = Object(enabled=False, required=True)
    content = Object(enabled=False, required=True)
    cookies = Object(enabled=False, required=False)

    url = Text(required=True)
    path = Text(required=True)
    mockau_traceparent = Keyword(required=False)
    text = Text(required=False)
    status_code = Integer(required=True)
    charset_encoding = Keyword(required=False)
    elapsed = Float(required=True)
    encoding = Keyword(required=False)
    http_version = Keyword(required=True)

    @classmethod
    def from_http_response(cls, response: HttpResponse) -> 'HttpResponseDocument':
        data = response.model_dump(mode='json')
        return cls(
            query_params=data['query_params'],
            socket_address=data.get('socket_address'),
            headers=data['headers'],
            content=data['content'],
            cookies=data['cookies'],
            url=str(response.get_full_url()),
            path=response.path,
            mockau_traceparent=response.mockau_traceparent,
            text=response.content.text,
            status_code=response.status_code,
            http_version=response.http_version,
            charset_encoding=response.charset_encoding,
            encoding=response.encoding,
            elapsed=response.elapsed,
        )

    def to_http_response(self) -> HttpResponse:
        data = self.to_dict()
        return HttpResponse(
            path=data['path'],
            query_params=data.get('query_params', list()),
            socket_address=data.get('socket_address'),
            headers=data.get('headers', HttpRequestHeaders()),
            status_code=data['status_code'],
            charset_encoding=data.get('charset_encoding'),
            elapsed=data['elapsed'],
            encoding=data.get('encoding'),
            content=data['content'],
            cookies=data.get('cookies', HttpRequestCookies()),
        )


class BaseHttpEventDocument(AsyncDocument):
    event = Keyword(required=True)
    created_at = Date(default_timezone=pytz.UTC, required=True)
    mockau_traceparent = Text(required=True)
    mockau_trace_id = Keyword(required=True)
    timestamp = Long(required=True)


class EventHttpRequestDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request'

    parent_mockau_traceparent = Keyword(required=False)
    http_request = Object(doc_class=HttpRequestDocument, required=True)

    def to_model(self) -> EventHttpRequestModel:
        return EventHttpRequestModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            parent_mockau_traceparent=self.parent_mockau_traceparent,
            http_request=self.http_request.to_http_request(),
        )


class EventHttpRequestErrorDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_error'

    def to_model(self) -> EventHttpRequestErrorModel:
        return EventHttpRequestErrorModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
        )


class EventHttpRequestActionDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_action'

    action_id = Keyword(required=True)

    def to_model(self) -> EventHttpRequestActionModel:
        return EventHttpRequestActionModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            action_id=self.action_id,
        )


class EventHttpResponseDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_response'

    http_response = Object(doc_class=HttpResponseDocument, required=True)

    def to_model(self) -> EventHttpResponseModel:
        return EventHttpResponseModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            http_response=self.http_response.to_http_response(),
        )


class EventHttpRequestResponseViewDocument(BaseHttpEventDocument):
    class Index:
        name = f'{MockauSettings.elk.index_prefix}_http_request_response_view'

    http_request = Object(doc_class=HttpRequestDocument, required=True)
    http_response = Object(doc_class=HttpResponseDocument, required=False)

    def to_model(self) -> EventHttpRequestResponseViewModel:
        return EventHttpRequestResponseViewModel(
            event=self.event,
            created_at=self.created_at,
            mockau_traceparent=self.mockau_traceparent,
            http_request=self.http_request.to_http_request(),
            http_response=self.http_response.to_http_response() if self.http_response else None,
        )


async def init_events(using: AsyncElasticsearch) -> None:
    tasks = [
        EventHttpRequestResponseViewDocument.init(using=using),
        EventHttpResponseDocument.init(using=using),
        EventHttpRequestActionDocument.init(using=using),
        EventHttpRequestErrorDocument.init(using=using),
        EventHttpRequestDocument.init(using=using),
    ]
    await asyncio.gather(*tasks)
