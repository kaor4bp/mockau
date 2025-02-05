import asyncio
from asyncio import create_task

from core.http.actions.types import t_HttpActionModel
from core.http.events.common import HttpEventType
from core.http.events.documents import (
    HttpRequestActionEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestEventDocument,
    HttpResponseEventDocument,
)
from core.http.events.models import (
    HttpRequestActionEventModel,
    HttpRequestErrorEventModel,
    HttpRequestEventModel,
    HttpResponseEventModel,
)
from core.http.interaction.schemas import HttpRequest
from core.http.interaction.schemas.http_response import HttpResponse
from dependencies import elasticsearch_client as es_client


class ProcessorEventsHandler:
    def __init__(self, inbound_http_request: HttpRequest) -> None:
        self.tasks = []
        self.inbound_http_request = inbound_http_request

    async def submit(self):
        await asyncio.gather(*self.tasks)
        self.tasks.clear()

    async def on_inbound_request_received(self):
        event = HttpRequestEventModel(
            event=(
                HttpEventType.HTTP_EXTERNAL_REQUEST
                if self.inbound_http_request.is_external
                else HttpEventType.HTTP_TRANSIT_REQUEST
            ),
            http_request=self.inbound_http_request,
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
        )
        self.tasks.append(create_task(HttpRequestEventDocument.from_model(event).save(using=es_client)))

    async def on_too_many_redirects_error(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
            mockau_traceparent=http_request.mockau_traceparent,
        )
        self.tasks.append(create_task(HttpRequestErrorEventDocument.from_model(event).save(using=es_client)))

    async def on_action_is_matched(self, action: t_HttpActionModel):
        event = HttpRequestActionEventModel(
            event=HttpEventType.HTTP_REQUEST_ACTION_MATCHED.value,
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
            action_id=action.id,
        )
        self.tasks.append(create_task(HttpRequestActionEventDocument.from_model(event).save(using=es_client)))

    async def on_actions_mismatched(self):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_REQUEST_ACTIONS_MISMATCHED.value,
            mockau_traceparent=self.inbound_http_request.mockau_traceparent,
        )
        self.tasks.append(
            create_task(HttpRequestErrorEventDocument.from_model(event).save(using=es_client)),
        )

    async def on_request_send(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST,
            mockau_traceparent=http_request.mockau_traceparent,
            http_request=http_request,
        )
        self.tasks.append(
            create_task(HttpRequestEventDocument.from_model(event).save(using=es_client)),
        )

    async def on_response_received(
        self,
        mockau_traceparent: str,
        http_response: HttpResponse,
    ):
        event = HttpResponseEventModel(
            event=HttpEventType.HTTP_RECEIVED_RESPONSE,
            mockau_traceparent=mockau_traceparent,
            http_response=http_response,
        )
        self.tasks.append(
            create_task(HttpResponseEventDocument.from_model(event).save(using=es_client)),
        )
