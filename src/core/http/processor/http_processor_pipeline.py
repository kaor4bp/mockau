from typing import AsyncGenerator

import httpx
from fastapi import BackgroundTasks
from httpx import Limits, Timeout
from pydantic import TypeAdapter

from core.http.actions.types import t_HttpActionModel
from core.http.interaction.schemas import HttpRequest
from core.http.interaction.schemas.http_response import HttpResponse
from core.http.processor.http_events_handler import HttpEventsHandler
from mockau_fastapi import MockauFastAPI
from models.storable_settings import DynamicEntrypoint, FollowRedirectsMode
from schemas.variables import VariablesContext


class HttpProcessorPipeline:
    def __init__(
        self,
        app: MockauFastAPI,
        background_tasks: BackgroundTasks,
        http_request: HttpRequest,
        entrypoint: str = 'default',
    ) -> None:
        self.app = app
        self.http_request = http_request
        self.events_handler = HttpEventsHandler(
            inbound_http_request=self.http_request,
            app=self.app,
            background_tasks=background_tasks,
        )
        self.entrypoint = entrypoint
        self.background_tasks = background_tasks

    async def get_http_client(self):
        if not self.app.state.clients.httpx_clients.get(self.entrypoint):
            de = await DynamicEntrypoint.get_by_name(self.app.state.clients, self.entrypoint)
            client = httpx.AsyncClient(
                http2=de.client_settings.http2,
                http1=de.client_settings.http1,
                follow_redirects=bool(de.client_settings.follow_redirects == FollowRedirectsMode.FOLLOWED_BY_CLIENT),
                max_redirects=de.client_settings.max_redirects,
                limits=Limits(
                    max_connections=100,
                    max_keepalive_connections=20,
                    keepalive_expiry=30 * 60,
                ),
                timeout=Timeout(
                    connect=30 * 60,
                    read=30 * 60,
                    write=30 * 60,
                    pool=30 * 60,
                ),
            )
            self.app.state.clients.httpx_clients[self.entrypoint] = (client, de.client_settings)
        return self.app.state.clients.httpx_clients[self.entrypoint]

    async def run(self) -> HttpResponse | None:
        await self.events_handler.on_inbound_request_received()
        action, context = await self.search_action()
        response = None
        if action:
            await self.events_handler.on_action_is_matched(action)
            client = await self.get_http_client()
            response = await action.execute(*client, self.events_handler)
            await self.events_handler.submit()
        else:
            await self.events_handler.on_actions_mismatched()
            await self.events_handler.submit()

        return response

    async def get_all_actions(self) -> AsyncGenerator[t_HttpActionModel, None]:
        query = (
            self.app.state.clients.mongo_actions_client.find(filters={'entrypoint': self.entrypoint, 'active': True})
            .sort({'priority': -1})
            .batch_size(100)
        )
        async for document in query:
            yield TypeAdapter(t_HttpActionModel).validate_python(document)

    async def search_action(self):
        try:
            async for action in self.get_all_actions():
                context = VariablesContext(variables_group=action.variables_group)
                is_matched = action.http_request.is_matched(self.http_request, context=context)
                # todo: add fetching of matching description
                if not is_matched:
                    await self.events_handler.on_action_mismatched_event(action, description='Not matched')
                    continue
                is_acquired = await action.acquire(self.app.state.clients)
                if is_matched and is_acquired:
                    return action, context
                else:
                    await self.events_handler.on_action_mismatched_event(action, description='Not acquired')
        except StopAsyncIteration:
            pass
        return None, None
