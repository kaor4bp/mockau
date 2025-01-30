from uuid import UUID, uuid4

from pydantic import Field

from models.base_model import BaseModel


class Times(BaseModel):
    remaining_times: int | None = None
    unlimited: bool = False


class TimeToLive(BaseModel):
    time_to_live: int | None = None


class AbstractAction(BaseModel):
    id: UUID = Field(default_factory=uuid4)
    priority: int
    entrypoint: str = 'default'
    times: Times | None = None
    time_to_live: TimeToLive | None = None
