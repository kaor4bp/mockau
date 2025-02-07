from enum import Enum


class HttpEventType(Enum):
    HTTP_SEND_REQUEST = 'http_send_request'

    HTTP_EXTERNAL_REQUEST = 'http_external_request'
    HTTP_TRANSIT_REQUEST = 'http_transit_request'
    HTTP_REQUEST_ACTION_MATCHED = 'http_request_action_matched'
    HTTP_REQUEST_NO_ACTION_FOUND = "http_request_no_action_found"

    HTTP_RECEIVED_RESPONSE = 'http_received_response'

    HTTP_REQUEST_TOO_MANY_REDIRECTS = 'http_request_too_many_redirects'

    HTTP_REQUEST_RESPONSE_VIEW = 'http_request_response_view'
    HTTP_ACTION_NOT_MATCHED_VIEW = 'http_action_not_matched_view'


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
        HttpEventType.HTTP_REQUEST_NO_ACTION_FOUND.value,
        HttpEventType.HTTP_RECEIVED_RESPONSE.value,
        HttpEventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
    ]
