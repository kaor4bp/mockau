from core.bases.base_model import BaseModel
from core.storable_settings.common import StorableSettingsType


class BaseStorableSettings(BaseModel):
    type_of: StorableSettingsType
