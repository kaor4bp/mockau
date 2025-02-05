from abc import abstractmethod
from uuid import UUID, uuid4

import httpx
from fastapi import Response
from pydantic import Field

from core.bases.base_model import BaseModel
from core.http.actions.common import Times, TimeToLive
from models.storable_settings import HttpClientSettings
from schemas.variables import VariablesGroup


class BaseHttpActionModel(BaseModel):
    id: UUID = Field(default_factory=uuid4)
    priority: int
    entrypoint: str = 'default'
    times: Times | None = None
    time_to_live: TimeToLive | None = None
    variables_group: VariablesGroup | None = None

    @abstractmethod
    async def execute(
        self,
        client: httpx.AsyncClient,
        client_settings: HttpClientSettings,
        events_handler: 'ProcessorEventsHandler',
    ) -> Response | None:
        pass
