from abc import ABC
from uuid import UUID, uuid4

from pydantic import Field

from core.bases.base_model_schema import BaseModelSchema
from core.http.actions.common import Times, TimeToLive


class BaseHttpAction(ABC, BaseModelSchema):
    id: UUID = Field(default_factory=uuid4)
    priority: int
    entrypoint: str = 'default'
    times: Times | None = None
    time_to_live: TimeToLive | None = None
