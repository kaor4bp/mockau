from asyncio import create_task, gather
from uuid import UUID

from dependencies import get_all_actions
from models.actions import OverrideHttpRequestAction, t_Action
from models.events import (
    EventExternalHttpRequest,
    EventHttpRequestActionMatched,
    EventHttpRequestActionsMismatched,
    EventInternalHttpRequest,
    EventReceivedHttpResponse,
    EventTransitHttpRequest,
)
from schemas import HttpRequest
from schemas.http_response import HttpResponse
from schemas.variables_context import VariablesContext


class HttpProcessorPipeline:
    def __init__(
        self,
        http_request: HttpRequest,
        entrypoint: str = 'default',
    ) -> None:
        self.http_request = http_request
        self.tasks = []
        self.entrypoint = entrypoint

    async def run(self) -> HttpResponse | None:
        await self.on_create()
        action, context = await self.search_action()
        if action:
            await self.on_action_is_matched(action)
            response = await self.execute_action(action)
            await gather(*self.tasks)
            return response
        else:
            await self.on_actions_mismatched()
            await gather(*self.tasks)
            return None

    async def execute_action(self, action: t_Action) -> HttpResponse:
        if isinstance(action, OverrideHttpRequestAction):
            new_request = action.http_request_override.override_http_request(self.http_request)
            await self.on_request_send(new_request)
            response = await new_request.send()
            await self.on_response_received(new_request.id, response)
            return response
        else:
            raise NotImplementedError()

    async def on_create(self):
        track_id = self.http_request.get_track_request_id()
        if track_id:
            event = EventTransitHttpRequest(track_http_request_id=track_id, http_request=self.http_request)
        else:
            event = EventExternalHttpRequest(http_request=self.http_request)
        self.tasks.append(create_task(event.send_to_mongo()))

    async def search_action(self):
        try:
            async for action in get_all_actions(self.entrypoint):
                context = VariablesContext()
                if action.http_request.is_matched(self.http_request, context=context):
                    return action, context
        except StopAsyncIteration:
            pass
        return None, None

    async def on_action_is_matched(self, action: t_Action):
        event = EventHttpRequestActionMatched(
            http_request_id=self.http_request.id,
            action_id=action.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_actions_mismatched(self):
        event = EventHttpRequestActionsMismatched(
            http_request_id=self.http_request.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_request_send(self, http_request: HttpRequest):
        event = EventInternalHttpRequest(
            track_http_request_id=http_request.id,
            http_request=http_request,
            parent_http_request_id=self.http_request.id,
        )
        self.tasks.append(create_task(event.send_to_mongo()))

    async def on_response_received(self, http_request_id: UUID, http_response: HttpResponse):
        event = EventReceivedHttpResponse(
            http_request_id=http_request_id,
            http_response=http_response,
        )
        self.tasks.append(create_task(event.send_to_mongo()))
