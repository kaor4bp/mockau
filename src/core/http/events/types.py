from typing import Union

from core.http.events.documents import (
    HttpRequestActionEventDocument,
    HttpRequestActionNotMatchedViewEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestEventDocument,
    HttpRequestResponseViewEventDocument,
    HttpResponseEventDocument,
)
from core.http.events.models import (
    HttpRequestActionEventModel,
    HttpRequestActionNotMatchedViewEventModel,
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
    HttpRequestActionNotMatchedViewEventModel,
]


t_EventDocument = Union[
    HttpRequestEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestActionEventDocument,
    HttpResponseEventDocument,
    HttpRequestResponseViewEventDocument,
    HttpRequestActionNotMatchedViewEventDocument,
]
