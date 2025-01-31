import asyncio
from asyncio import create_task
from uuid import UUID

from models.actions import t_Action
from models.events import (
    EventExternalHttpRequest,
    EventHttpRequestActionMatched,
    EventHttpRequestActionsMismatched,
    EventHttpRequestTooManyRedirects,
    EventInternalHttpRequest,
    EventReceivedHttpResponse,
    EventTransitHttpRequest,
)
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
        track_id = self.inbound_http_request.get_track_request_id()
        if track_id:
            event = EventTransitHttpRequest(track_http_request_id=track_id, http_request=self.inbound_http_request)
        else:
            event = EventExternalHttpRequest(http_request=self.inbound_http_request)
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_too_many_redirects_error(self, http_request: HttpRequest):
        event = EventHttpRequestTooManyRedirects(
            http_request_id=http_request.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_action_is_matched(self, action: t_Action):
        event = EventHttpRequestActionMatched(
            http_request_id=self.inbound_http_request.id,
            action_id=action.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_actions_mismatched(self):
        event = EventHttpRequestActionsMismatched(
            http_request_id=self.inbound_http_request.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_request_send(self, http_request: HttpRequest):
        event = EventInternalHttpRequest(
            track_http_request_id=http_request.id,
            http_request=http_request,
            parent_http_request_id=self.inbound_http_request.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_response_received(self, http_request_id: UUID, http_response: HttpResponse):
        event = EventReceivedHttpResponse(
            http_request_id=http_request_id,
            http_response=http_response,
        )
        self.tasks.append(create_task(event.send_to_mongo()))
