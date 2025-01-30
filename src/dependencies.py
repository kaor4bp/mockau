from typing import Generator

from pydantic import TypeAdapter

from models.actions import t_Action
from utils.mongo import MongoClient

mongo_events_client = MongoClient(collection='mockau_events')
mongo_actions_client = MongoClient(collection='mockau_actions')
mongo_settings_client = MongoClient(collection='mockau_settings')


async def get_all_actions(entrypoint: str) -> Generator[t_Action, None, None]:
    query = mongo_actions_client.find(filters={'entrypoint': entrypoint}).sort({'priority': -1}).batch_size(100)
    async for document in query:
        yield TypeAdapter(t_Action).validate_python(document)
