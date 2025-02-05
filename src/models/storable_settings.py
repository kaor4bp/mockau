from enum import Enum
from typing import Literal

from pydantic import Field

from core.bases.base_model import BaseModel
from mockau_fastapi import MockauFastAPI


class StorableSettingsType(Enum):
    DYNAMIC_ENTRYPOINT = 'DYNAMIC_ENTRYPOINT'


class BaseStorableSettings(BaseModel):
    type_of: StorableSettingsType


class FollowRedirectsMode(Enum):
    FOLLOWED_BY_CLIENT = 'FOLLOWED_BY_CLIENT'
    FOLLOWED_BY_MOCK = 'FOLLOWED_BY_MOCK'
    NO_FOLLOW = 'NO_FOLLOW'


class HttpClientSettings(BaseModel):
    http1: bool = True
    http2: bool = True
    follow_redirects: FollowRedirectsMode = FollowRedirectsMode.FOLLOWED_BY_CLIENT
    max_redirects: int = 20


class DynamicEntrypoint(BaseModel):
    type_of: Literal['DYNAMIC_ENTRYPOINT'] = 'DYNAMIC_ENTRYPOINT'
    name: str
    client_settings: HttpClientSettings = Field(default_factory=HttpClientSettings)

    @classmethod
    async def get_all(cls, app: MockauFastAPI) -> list['DynamicEntrypoint']:
        documents = await app.state.mongo_settings_client.find(
            filters={'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        ).to_list()
        return [cls.model_validate(document) for document in documents]

    @classmethod
    async def get_by_name(cls, app: MockauFastAPI, name: str) -> 'DynamicEntrypoint':
        document = await app.state.mongo_settings_client.find_one(filters={'name': name})
        return cls.model_validate(document)

    async def create(self, app: MockauFastAPI) -> None:
        await app.state.mongo_settings_client.insert_one(self.model_dump(mode='json'))

    async def delete(self, app: MockauFastAPI) -> None:
        await app.state.mongo_settings_client.delete_many(
            {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        )

    async def exists(self, app: MockauFastAPI) -> bool:
        return bool(
            await app.state.mongo_settings_client.find_one(
                {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
            )
        )
