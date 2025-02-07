import httpx

from core.http.actions.models.base_http_action_model import BaseHttpActionModel
from core.http.interaction.schemas.http_response import HttpResponse
from models.storable_settings import HttpClientSettings


class StubHttpResponseActionModel(BaseHttpActionModel):
    http_response: HttpResponse

    async def execute(
        self,
        client: httpx.AsyncClient,
        client_settings: HttpClientSettings,
        events_handler: 'HttpEventsHandler',
    ):
        await events_handler.on_response_received(
            events_handler.inbound_http_request.mockau_traceparent,
            self.http_response,
        )
        return self.http_response
