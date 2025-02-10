from datetime import datetime

import pytz
from pydantic import Field

from core.bases.base_model import BaseModel
from core.http.events.common import HttpEventType


class BaseHttpEventModel(BaseModel):
    event: HttpEventType
    created_at: datetime = Field(default_factory=lambda: datetime.now(tz=pytz.UTC))
    mockau_traceparent: str
    traceparent: str | None = None
    level: str

    @property
    def timestamp(self) -> int:
        return int(self.created_at.timestamp() * 1000000)

    @property
    def mockau_trace_id(self) -> str:
        _, trace_id, _, _ = self.mockau_traceparent.split('-')
        return trace_id
