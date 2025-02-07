from abc import abstractmethod
from datetime import datetime
from uuid import UUID, uuid4

import httpx
import pytz
from fastapi import Response
from pydantic import Field

from core.bases.base_model import BaseModel
from core.http.actions.common import Times, TimeToLive
from mockau_fastapi import MockauSharedClients
from models.storable_settings import HttpClientSettings
from schemas.variables import VariablesGroup


class BaseHttpActionModel(BaseModel):
    id: UUID = Field(default_factory=uuid4)
    priority: int
    entrypoint: str = 'default'
    times: Times | None = None
    time_to_live: TimeToLive | None = None
    variables_group: VariablesGroup = Field(default_factory=VariablesGroup)

    # internal fields

    active: bool = True
    created_at: datetime = Field(default_factory=lambda: datetime.now(tz=pytz.UTC))
    revision: UUID = Field(default_factory=uuid4)
    hits: int = 0

    async def acquire(self, clients: MockauSharedClients) -> bool:
        filters = {'id': str(self.id), 'active': True, 'revision': str(self.revision)}
        if self.times and self.times.unlimited is False:
            filters['hits'] = {'$lt': self.times.remaining_times}
        if self.time_to_live and self.time_to_live.time_to_live is not None:
            filters['created_at'] = {'$gt': datetime.now(tz=pytz.UTC) - self.time_to_live.to_timedelta()}

        update_result = await clients.mongo_actions_client.update_one(filters=filters, update={"$inc": {"hits": 1}})
        if update_result.modified_count == 0:
            await clients.mongo_actions_client.update_one(
                filters={'id': str(self.id), 'revision': str(self.revision)},
                update={'$set': {'active': False}},
            )
            return False
        else:
            return True

    @abstractmethod
    async def execute(
        self,
        client: httpx.AsyncClient,
        client_settings: HttpClientSettings,
        events_handler: 'HttpEventsHandler',
    ) -> Response | None:
        pass
