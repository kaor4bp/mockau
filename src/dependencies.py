from typing import Generator

from pydantic import TypeAdapter

from models.actions import t_Action
from utils.mongo import MongoClient

mongo_events_manager = MongoClient(collection='mockau_events')
mongo_actions_manager = MongoClient(collection='mockau_actions')


async def get_all_actions() -> Generator[t_Action, None, None]:
    query = mongo_actions_manager.find(filters={}).sort({'priority': -1}).batch_size(100)
    while query.alive:
        document = await query.next()
        yield TypeAdapter(t_Action).validate_python(document)
