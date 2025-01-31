from models.actions.abstract_action import AbstractAction
from schemas.http_request.http_request import FollowRedirectsMode
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher
from schemas.http_request_modify.http_request import HttpRequestModify
from schemas.http_request_override.http_request import HttpRequestOverride
from schemas.http_response import HttpResponse


class OverrideHttpRequestAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_request_override: HttpRequestOverride

    async def execute(self, events_handler: 'ProcessorEventsHandler'):
        new_request = self.http_request_override.override_http_request(events_handler.inbound_http_request)
        client = new_request.get_client()
        response = None

        for _ in range(new_request.client_settings.max_redirects):
            await events_handler.on_request_send(new_request)
            response = await new_request.send(client)
            await events_handler.on_response_received(new_request.id, response)

            if (
                new_request.client_settings.follow_redirects is FollowRedirectsMode.FOLLOWED_BY_MOCK
                and 300 <= response.status_code < 400
                and response.has_redirect_location
            ):
                new_request = new_request.follow_redirect(response)
            else:
                break
        else:
            await events_handler.on_too_many_redirects_error(new_request)

        return response


class ModifyHttpRequestAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_request_modify: HttpRequestModify


class StubHttpResponseAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_response: HttpResponse

    async def execute(self, events_handler: 'ProcessorEventsHandler'):
        await events_handler.on_response_received(events_handler.inbound_http_request.id, self.http_response)
        return self.http_response
