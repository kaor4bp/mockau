from typing import Union

from core.http.events.documents import (
    HttpRequestActionEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestEventDocument,
    HttpRequestResponseViewEventDocument,
    HttpResponseEventDocument,
)
from core.http.events.models import (
    HttpRequestActionEventModel,
    HttpRequestErrorEventModel,
    HttpRequestEventModel,
    HttpRequestResponseViewEventModel,
    HttpResponseEventModel,
)

t_EventModel = Union[
    HttpRequestEventModel,
    HttpRequestErrorEventModel,
    HttpRequestActionEventModel,
    HttpResponseEventModel,
    HttpRequestResponseViewEventModel,
]


t_EventDocument = Union[
    HttpRequestEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestActionEventDocument,
    HttpResponseEventDocument,
    HttpRequestResponseViewEventDocument,
]
