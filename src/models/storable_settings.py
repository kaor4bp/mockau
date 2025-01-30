from enum import Enum
from typing import Literal

from dependencies import mongo_settings_client
from models.base_model import BaseModel


class StorableSettingsType(Enum):
    DYNAMIC_ENTRYPOINT = 'DYNAMIC_ENTRYPOINT'


class BaseStorableSettings(BaseModel):
    type_of: StorableSettingsType


class DynamicEntrypoint(BaseModel):
    type_of: Literal['DYNAMIC_ENTRYPOINT'] = 'DYNAMIC_ENTRYPOINT'
    name: str

    @classmethod
    async def get_all(cls) -> list['DynamicEntrypoint']:
        documents = await mongo_settings_client.find(
            filters={'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        ).to_list()
        return [cls.model_validate(document) for document in documents]

    async def create(self) -> None:
        await mongo_settings_client.insert_one(self.model_dump(mode='json'))

    async def delete(self) -> None:
        await mongo_settings_client.delete_one(
            {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
        )

    async def exists(self) -> bool:
        return bool(
            await mongo_settings_client.find_one(
                {'name': self.name, 'type_of': StorableSettingsType.DYNAMIC_ENTRYPOINT.value}
            )
        )
