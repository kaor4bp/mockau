import asyncio
from asyncio import create_task
from datetime import datetime

import pytz

from dependencies import elasticsearch_client as es_client
from es_documents.events import (
    EventHttpRequestActionDocument,
    EventHttpRequestDocument,
    EventHttpRequestErrorDocument,
    EventHttpResponseDocument,
    HttpRequestDocument,
    HttpResponseDocument,
)
from models.actions import t_Action
from models.events import EventType
from schemas import HttpRequest
from schemas.http_response import HttpResponse


class ProcessorEventsHandler:
    def __init__(self, inbound_http_request: HttpRequest) -> None:
        self.tasks = []
        self.inbound_http_request = inbound_http_request

    async def submit(self):
        await asyncio.gather(*self.tasks)
        self.tasks.clear()

    async def on_inbound_request_received(self):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpRequestDocument(
            event=(
                EventType.HTTP_EXTERNAL_REQUEST.value
                if self.inbound_http_request.is_external
                else EventType.HTTP_TRANSIT_REQUEST.value
            ),
            created_at=create_at,
            timestamp=int(create_at.timestamp() * 1000000),
            http_request=HttpRequestDocument.from_http_request(self.inbound_http_request),
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
            mockau_trace_id=self.inbound_http_request.mockau_trace_id,
        )
        self.tasks.append(create_task(event.save(using=es_client)))

    async def on_too_many_redirects_error(
        self,
        http_request: HttpRequest,
    ):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpRequestErrorDocument(
            event=EventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
            mockau_traceparent=http_request.mockau_traceparent,
            mockau_trace_id=http_request.mockau_trace_id,
            created_at=datetime.now(tz=pytz.UTC),
            timestamp=int(create_at.timestamp() * 1000000),
        )
        self.tasks.append(create_task(event.save(using=es_client)))

    async def on_action_is_matched(self, action: t_Action):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpRequestActionDocument(
            event=EventType.HTTP_REQUEST_ACTION_MATCHED.value,
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
            mockau_trace_id=self.inbound_http_request.mockau_trace_id,
            action_id=str(action.id),
            created_at=datetime.now(tz=pytz.UTC),
            timestamp=int(create_at.timestamp() * 1000000),
        )
        self.tasks.append(create_task(event.save(using=es_client)))

    async def on_actions_mismatched(self):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpRequestErrorDocument(
            event=EventType.HTTP_REQUEST_ACTIONS_MISMATCHED.value,
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
            mockau_trace_id=self.inbound_http_request.mockau_trace_id,
            created_at=datetime.now(tz=pytz.UTC),
            timestamp=int(create_at.timestamp() * 1000000),
        )
        self.tasks.append(create_task(event.save(using=es_client)))

    async def on_request_send(
        self,
        http_request: HttpRequest,
    ):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpRequestDocument(
            event=EventType.HTTP_SEND_REQUEST.value,
            mockau_traceparent=http_request.mockau_traceparent,
            mockau_trace_id=http_request.mockau_trace_id,
            http_request=HttpRequestDocument.from_http_request(http_request),
            mockau_parent_traceparent=self.inbound_http_request.mockau_traceparent,
            created_at=datetime.now(tz=pytz.UTC),
            timestamp=int(create_at.timestamp() * 1000000),
        )
        self.tasks.append(create_task(event.save(using=es_client)))

    async def on_response_received(
        self,
        mockau_traceparent: str,
        http_response: HttpResponse,
    ):
        create_at = datetime.now(tz=pytz.UTC)
        event = EventHttpResponseDocument(
            event=EventType.HTTP_RECEIVED_RESPONSE.value,
            mockau_traceparent=mockau_traceparent,
            mockau_trace_id=self.inbound_http_request.mockau_trace_id,
            http_response=HttpResponseDocument.from_http_response(http_response),
            created_at=datetime.now(tz=pytz.UTC),
            timestamp=int(create_at.timestamp() * 1000000),
        )
        self.tasks.append(create_task(event.save(using=es_client)))
