from pydantic import TypeAdapter

from schemas.actions import t_Action
from utils.mongo import MongoClient

mongo_events_manager = MongoClient(collection='mockau_events')
mongo_actions_manager = MongoClient(collection='mockau_actions')


async def get_all_actions() -> list[t_Action]:
    documents = await mongo_actions_manager.find(filters={}).sort({'priority': 1}).to_list()
    return [TypeAdapter(t_Action).validate_python(document) for document in documents]
