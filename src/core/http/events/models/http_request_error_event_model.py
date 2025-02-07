from typing import Literal

from core.http.events.models.base_http_event_model import BaseHttpEventModel


class HttpRequestErrorEventModel(BaseHttpEventModel):
    event: Literal['http_request_too_many_redirects', 'http_request_actions_mismatched', 'http_request_no_action_found']
