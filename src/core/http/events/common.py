from enum import Enum


class HttpEventType(Enum):
    HTTP_SEND_REQUEST = 'http_send_request'

    HTTP_EXTERNAL_REQUEST = 'http_external_request'
    HTTP_TRANSIT_REQUEST = 'http_transit_request'
    HTTP_REQUEST_ACTION_MATCHED = 'http_request_action_matched'
    HTTP_REQUEST_ACTIONS_MISMATCHED = 'http_request_actions_mismatched'

    HTTP_RECEIVED_RESPONSE = 'http_received_response'

    HTTP_REQUEST_TOO_MANY_REDIRECTS = 'http_request_too_many_redirects'

    HTTP_REQUEST_RESPONSE_VIEW = 'http_request_response_view'


class HttpEventTypeGroup:
    ALL_HTTP_REQUEST = [
        HttpEventType.HTTP_EXTERNAL_REQUEST.value,
        HttpEventType.HTTP_SEND_REQUEST.value,
        HttpEventType.HTTP_TRANSIT_REQUEST.value,
    ]
    INBOUND_HTTP_REQUEST = [
        HttpEventType.HTTP_EXTERNAL_REQUEST.value,
        HttpEventType.HTTP_TRANSIT_REQUEST.value,
    ]
    NON_LAZY_EVENTS = [
        HttpEventType.HTTP_SEND_REQUEST.value,
        HttpEventType.HTTP_EXTERNAL_REQUEST.value,
        HttpEventType.HTTP_TRANSIT_REQUEST.value,
        HttpEventType.HTTP_REQUEST_ACTION_MATCHED.value,
        HttpEventType.HTTP_REQUEST_ACTIONS_MISMATCHED.value,
        HttpEventType.HTTP_RECEIVED_RESPONSE.value,
        HttpEventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
    ]
