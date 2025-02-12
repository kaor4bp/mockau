from enum import Enum

from core.bases.base_model import BaseModel


class StorableSettingsType(Enum):
    DYNAMIC_ENTRYPOINT = 'DYNAMIC_ENTRYPOINT'
    SHARED_SECRET_KEY = 'SHARED_SECRET_KEY'


class FollowRedirectsMode(Enum):
    FOLLOWED_BY_CLIENT = 'FOLLOWED_BY_CLIENT'
    FOLLOWED_BY_MOCK = 'FOLLOWED_BY_MOCK'
    NO_FOLLOW = 'NO_FOLLOW'


class HttpClientSettings(BaseModel):
    http1: bool = True
    http2: bool = True
    follow_redirects: FollowRedirectsMode = FollowRedirectsMode.FOLLOWED_BY_CLIENT
    max_redirects: int = 20
