from datetime import datetime
from typing import Optional

import pytz
from elasticsearch_dsl import Date, Keyword, Long, Text

from core.bases.base_model_async_document import BaseModelAsyncDocument


class BaseHttpEventDocument(BaseModelAsyncDocument):
    event: str = Keyword(required=True)
    created_at: datetime = Date(default_timezone=pytz.UTC, required=True)
    mockau_traceparent: str = Text(required=True)
    mockau_trace_id: str = Keyword(required=True)
    timestamp: int = Long(required=True)
    traceparent: Optional[str] = Keyword(required=False)
    level: str = Keyword(required=True)
