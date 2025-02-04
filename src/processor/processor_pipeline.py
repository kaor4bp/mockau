from datetime import datetime
from typing import Generator

import httpx
import pytz
from fastapi import BackgroundTasks
from httpx import Limits, Timeout
from pydantic import TypeAdapter

from dependencies import elasticsearch_client as es_client
from dependencies import mongo_actions_client
from es_documents.events import EventHttpRequestResponseViewDocument, HttpRequestDocument, HttpResponseDocument
from models.actions import t_Action
from models.events import EventType
from models.storable_settings import DynamicEntrypoint, FollowRedirectsMode, HttpClientSettings
from processor.processor_events_handler import ProcessorEventsHandler
from schemas import HttpRequest
from schemas.http_response import HttpResponse
from schemas.variables import VariablesContext, VariablesGroup


class HttpProcessorPipeline:
    HTTP_CLIENTS = {
        'default': (
            httpx.AsyncClient(http1=True, http2=True, follow_redirects=True, max_redirects=20),
            HttpClientSettings(),
        ),
    }

    def __init__(
        self,
        background_tasks: BackgroundTasks,
        http_request: HttpRequest,
        entrypoint: str = 'default',
    ) -> None:
        self.http_request = http_request
        self.events_handler = ProcessorEventsHandler(self.http_request)
        self.entrypoint = entrypoint
        self.background_tasks = background_tasks

    async def get_http_client(self):
        if not HttpProcessorPipeline.HTTP_CLIENTS.get(self.entrypoint):
            de = await DynamicEntrypoint.get_by_name(self.entrypoint)
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
            HttpProcessorPipeline.HTTP_CLIENTS[self.entrypoint] = (client, de.client_settings)
        return HttpProcessorPipeline.HTTP_CLIENTS[self.entrypoint]

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

        if self.http_request.is_external:
            created_at = datetime.now(tz=pytz.UTC)
            request_response_view_event = EventHttpRequestResponseViewDocument(
                event=EventType.HTTP_REQUEST_RESPONSE_VIEW.value,
                http_request=HttpRequestDocument.from_http_request(self.http_request),
                http_response=HttpResponseDocument.from_http_response(response) if response else None,
                mockau_traceparent=self.http_request.mockau_traceparent,
                mockau_trace_id=self.http_request.mockau_trace_id,
                created_at=created_at,
                timestamp=int(created_at.timestamp() * 1000000),
            )
            self.background_tasks.add_task(request_response_view_event.save, using=es_client)
        return response

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
