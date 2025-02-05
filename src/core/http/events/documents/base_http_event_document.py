from datetime import datetime

import pytz
from elasticsearch_dsl import Date, Keyword, Long, Text

from core.bases.base_model_async_document import BaseModelAsyncDocument


class BaseHttpEventDocument(BaseModelAsyncDocument):
    event: str = Keyword(required=True)
    created_at: datetime = Date(default_timezone=pytz.UTC, required=True)
    mockau_traceparent: str = Text(required=True)
    mockau_trace_id: str = Keyword(required=True)
    timestamp: int = Long(required=True)
