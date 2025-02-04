from datetime import datetime
from enum import Enum
from typing import Literal, Optional, Union
from uuid import UUID

from models.base_model import BaseModel
from schemas import HttpRequest
from schemas.http_response import HttpResponse


class EventType(Enum):
    HTTP_SEND_REQUEST = 'http_send_request'

    HTTP_EXTERNAL_REQUEST = 'http_external_request'
    HTTP_TRANSIT_REQUEST = 'http_transit_request'
    HTTP_REQUEST_ACTION_MATCHED = 'http_request_action_matched'
    HTTP_REQUEST_ACTIONS_MISMATCHED = 'http_request_actions_mismatched'

    HTTP_RECEIVED_RESPONSE = 'http_received_response'

    HTTP_REQUEST_TOO_MANY_REDIRECTS = 'http_request_too_many_redirects'

    HTTP_REQUEST_RESPONSE_VIEW = 'http_request_response_view'


class EventTypeGroup:
    ALL_HTTP_REQUEST = [
        EventType.HTTP_EXTERNAL_REQUEST.value,
        EventType.HTTP_SEND_REQUEST.value,
        EventType.HTTP_TRANSIT_REQUEST.value,
    ]
    INBOUND_HTTP_REQUEST = [
        EventType.HTTP_EXTERNAL_REQUEST.value,
        EventType.HTTP_TRANSIT_REQUEST.value,
    ]
    NON_LAZY_EVENTS = [
        EventType.HTTP_SEND_REQUEST.value,
        EventType.HTTP_EXTERNAL_REQUEST.value,
        EventType.HTTP_TRANSIT_REQUEST.value,
        EventType.HTTP_REQUEST_ACTION_MATCHED.value,
        EventType.HTTP_REQUEST_ACTIONS_MISMATCHED.value,
        EventType.HTTP_RECEIVED_RESPONSE.value,
        EventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
    ]


class BaseHttpEventModel(BaseModel):
    event: EventType
    created_at: datetime
    mockau_traceparent: str


class EventHttpRequestModel(BaseHttpEventModel):
    parent_mockau_traceparent: str | None = None
    http_request: HttpRequest


class EventHttpRequestErrorModel(BaseHttpEventModel):
    event: Literal[
        'http_request_too_many_redirects',
        'http_request_actions_mismatched',
    ]


class EventHttpRequestActionModel(BaseHttpEventModel):
    action_id: UUID


class EventHttpResponseModel(BaseHttpEventModel):
    http_response: HttpResponse


class EventHttpRequestResponseViewModel(BaseHttpEventModel):
    http_request: HttpRequest
    http_response: Optional[HttpResponse] = None


t_EventModel = Union[
    EventHttpRequestModel,
    EventHttpRequestErrorModel,
    EventHttpRequestActionModel,
    EventHttpResponseModel,
    EventHttpRequestResponseViewModel,
]
