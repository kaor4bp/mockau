from typing import Literal

from pydantic import Field

from core.storable_settings.common import HttpClientSettings, StorableSettingsType
from core.storable_settings.models.base_storable_settings import BaseStorableSettings
from mockau_fastapi import MockauSharedClients


class DynamicEntrypoint(BaseStorableSettings):
    type_of: Literal['DYNAMIC_ENTRYPOINT'] = 'DYNAMIC_ENTRYPOINT'
    name: str
    client_settings: HttpClientSettings = Field(default_factory=HttpClientSettings)

    @classmethod
    async def get_all(cls, clients: MockauSharedClients) -> list['DynamicEntrypoint']:
        documents = await clients.mongo_settings_client.find(
            filters={'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        ).to_list()
        return [cls.model_validate(document) for document in documents]

    @classmethod
    async def get_by_name(cls, clients: MockauSharedClients, name: str) -> 'DynamicEntrypoint':
        document = await clients.mongo_settings_client.find_one(filters={'name': name})
        return cls.model_validate(document)

    async def create(self, clients: MockauSharedClients) -> None:
        await clients.mongo_settings_client.insert_one(self.model_dump(mode='json'))

    async def delete(self, clients: MockauSharedClients) -> None:
        await clients.mongo_settings_client.delete_many(
            {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        )

    async def exists(self, clients: MockauSharedClients) -> bool:
        return bool(
            await clients.mongo_settings_client.find_one(
                {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
            )
        )
