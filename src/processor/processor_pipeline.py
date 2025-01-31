from typing import Generator

from pydantic import TypeAdapter

from dependencies import mongo_actions_client
from models.actions import t_Action
from processor.processor_events_handler import ProcessorEventsHandler
from schemas import HttpRequest
from schemas.http_response import HttpResponse
from schemas.variables import VariablesContext, VariablesGroup


class HttpProcessorPipeline:
    def __init__(
        self,
        http_request: HttpRequest,
        entrypoint: str = 'default',
    ) -> None:
        self.http_request = http_request
        self.events_handler = ProcessorEventsHandler(self.http_request)
        self.entrypoint = entrypoint

    async def run(self) -> HttpResponse | None:
        await self.events_handler.on_inbound_request_received()
        action, context = await self.search_action()
        if action:
            await self.events_handler.on_action_is_matched(action)
            response = await action.execute(self.events_handler)
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
