from abc import abstractmethod
from uuid import UUID, uuid4

import httpx
from fastapi import Response
from pydantic import Field

from models.base_model import BaseModel
from models.storable_settings import HttpClientSettings
from schemas.variables import VariablesGroup


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
    variables_group: VariablesGroup | None = None

    @abstractmethod
    async def execute(
        self, client: httpx.AsyncClient, client_settings: HttpClientSettings, events_handler: 'ProcessorEventsHandler'
    ) -> Response | None:
        pass
