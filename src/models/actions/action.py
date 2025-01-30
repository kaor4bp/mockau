from models.actions.abstract_action import AbstractAction
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher
from schemas.http_request_modify.http_request import HttpRequestModify
from schemas.http_request_override.http_request import HttpRequestOverride
from schemas.http_response import HttpResponse


class OverrideHttpRequestAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_request_override: HttpRequestOverride


class ModifyHttpRequestAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_request_modify: HttpRequestModify


class StubHttpResponseAction(AbstractAction):
    http_request: HttpRequestMatcher
    http_response: HttpResponse
