import os
import pathlib
from functools import cached_property

from dotenv import load_dotenv

load_dotenv(
    dotenv_path=str(pathlib.Path(__file__).parent.parent.joinpath('./.env').resolve()),
    verbose=True,
)


def StringConfigItem(env: str, default: str | None = None) -> str:
    def get_env(self):
        value = os.getenv(env, default=default)
        assert value is not None, f'Environment variable {env} is not set'
        return value

    return cached_property(get_env)


def BooleanConfigItem(env: str, default: bool | None = None) -> str:
    def get_env(self):
        value = os.getenv(env, default=default)
        assert value is not None, f'Environment variable {env} is not set'
        if isinstance(value, str):
            value = value.lower() == 'true'
        return value

    return cached_property(get_env)


class _MongoSettings:
    uri: str = StringConfigItem(env='MONGO_URI')
    db_name: str = StringConfigItem(env='MONGO_DB_NAME')


class _ELKSettings:
    uri: str = StringConfigItem(env='ELASTICSEARCH_URI')
    index_prefix: str = StringConfigItem(env='ELASTICSEARCH_INDEX_PREFIX', default='mockau')


class _RedisSettings:
    uri: str = StringConfigItem(env='REDIS_URI')


class _PathSettings:
    root_path = pathlib.Path(__file__).parent.parent.resolve()
    src_path = pathlib.Path(__file__).parent.resolve()

    _content: str = StringConfigItem(env='PATH_CONTENT', default='./content')

    @property
    def content_path(self) -> pathlib.Path:
        content_path = pathlib.Path(self._content).resolve()
        if content_path.is_absolute():
            return content_path
        else:
            return self.root_path.joinpath(content_path)


class MockauSettings:
    mongo: _MongoSettings = _MongoSettings()
    elk: _ELKSettings = _ELKSettings()
    redis: _RedisSettings = _RedisSettings()
    path: _PathSettings = _PathSettings()

    @classmethod
    async def on_startup(cls) -> None:
        content_path = pathlib.Path(cls.path.content)
        if not content_path.exists():
            content_path.mkdir(parents=True)


if __name__ == '__main__':
    print(MockauSettings.path.root_path)
    print(MockauSettings.path.src_path)
    print(MockauSettings.path.content_path)
