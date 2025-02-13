import httpx

from core.http.actions.models.base_http_action_model import BaseHttpActionModel
from core.storable_settings.common import FollowRedirectsMode, HttpClientSettings
from schemas.http_request_override.http_request import HttpRequestOverride


class HttpRequestOverrideActionModel(BaseHttpActionModel):
    http_request_override: HttpRequestOverride

    async def execute(
        self,
        client: httpx.AsyncClient,
        client_settings: HttpClientSettings,
        events_handler: 'HttpEventsHandler',  # noqa: F821
    ):
        new_request = self.http_request_override.override_http_request(events_handler.inbound_http_request)
        response = None

        for _ in range(client_settings.max_redirects):
            await events_handler.on_request_send(new_request)

            try:
                response = await new_request.send(client)
            except httpx.ReadTimeout:
                await events_handler.on_send_request_read_timeout(new_request)
            except httpx.ConnectTimeout:
                await events_handler.on_send_request_connect_timeout(new_request)
            except httpx.PoolTimeout:
                await events_handler.on_send_request_pool_timeout(new_request)
            except httpx.WriteError:
                await events_handler.on_send_request_write_error(new_request)

            await events_handler.on_response_received(new_request.mockau_traceparent, response)
            await events_handler.on_request_response_view_event(new_request, response)

            if (
                client_settings.follow_redirects is FollowRedirectsMode.FOLLOWED_BY_MOCK
                and 300 <= response.status_code < 400
                and response.has_redirect_location
            ):
                new_request = new_request.follow_redirect(response)
            else:
                break
        else:
            await events_handler.on_too_many_redirects_error(new_request)

        return response
