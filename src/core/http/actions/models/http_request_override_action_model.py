import httpx

from core.http.actions.models.base_http_action_model import BaseHttpActionModel
from models.storable_settings import FollowRedirectsMode, HttpClientSettings
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher
from schemas.http_request_override.http_request import HttpRequestOverride


class HttpRequestOverrideActionModel(BaseHttpActionModel):
    http_request: HttpRequestMatcher
    http_request_override: HttpRequestOverride

    async def execute(
        self,
        client: httpx.AsyncClient,
        client_settings: HttpClientSettings,
        events_handler: 'HttpEventsHandler',
    ):
        new_request = self.http_request_override.override_http_request(events_handler.inbound_http_request)
        response = None

        for _ in range(client_settings.max_redirects):
            await events_handler.on_request_send(new_request)
            response = await new_request.send(client)
            await events_handler.on_response_received(new_request.mockau_traceparent, response)

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
