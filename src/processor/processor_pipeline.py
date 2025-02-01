from typing import Generator

import httpx
from pydantic import TypeAdapter

from dependencies import mongo_actions_client
from models.actions import t_Action
from models.storable_settings import DynamicEntrypoint, FollowRedirectsMode, HttpClientSettings
from processor.processor_events_handler import ProcessorEventsHandler
from schemas import HttpRequest
from schemas.http_response import HttpResponse
from schemas.variables import VariablesContext, VariablesGroup

_HTTP_CLIENTS = {
    'default': (
        httpx.AsyncClient(http1=True, http2=True, follow_redirects=True, max_redirects=20),
        HttpClientSettings(),
    ),
}


class HttpProcessorPipeline:
    def __init__(
        self,
        http_request: HttpRequest,
        entrypoint: str = 'default',
    ) -> None:
        self.http_request = http_request
        self.events_handler = ProcessorEventsHandler(self.http_request)
        self.entrypoint = entrypoint

    async def get_http_client(self):
        if not _HTTP_CLIENTS.get(self.entrypoint):
            de = await DynamicEntrypoint.get_by_name(self.entrypoint)
            client = httpx.AsyncClient(
                http2=de.client_settings.http2,
                http1=de.client_settings.http1,
                follow_redirects=bool(de.client_settings.follow_redirects == FollowRedirectsMode.FOLLOWED_BY_CLIENT),
                max_redirects=de.client_settings.max_redirects,
            )
            _HTTP_CLIENTS[self.entrypoint] = (client, de.client_settings)
        return _HTTP_CLIENTS[self.entrypoint]

    async def run(self) -> HttpResponse | None:
        await self.events_handler.on_inbound_request_received()
        action, context = await self.search_action()
        if action:
            await self.events_handler.on_action_is_matched(action)
            client = await self.get_http_client()
            response = await action.execute(*client, self.events_handler)
            await self.events_handler.submit()
            return response
        else:
            await self.events_handler.on_actions_mismatched()
            await self.events_handler.submit()
            return None

    async def get_all_actions(self) -> Generator[t_Action, None, None]:
        query = (
            mongo_actions_client.find(filters={'entrypoint': self.entrypoint}).sort({'priority': -1}).batch_size(100)
        )
        async for document in query:
            yield TypeAdapter(t_Action).validate_python(document)

    async def search_action(self):
        try:
            async for action in self.get_all_actions():
                context = VariablesContext(variables_group=action.variables_group or VariablesGroup())
                if action.http_request.is_matched(self.http_request, context=context):
                    return action, context
        except StopAsyncIteration:
            pass
        return None, None
