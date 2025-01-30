import asyncio

from pydantic import TypeAdapter

from dependencies import mongo_events_client
from models.events import EventTypeGroup, t_HttpRequestEvent


async def group_events(recursion_limit: int = 5):
    document = await mongo_events_client.find_one(
        filters={
            'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            '$or': [{'group_id': None}, {'group_id': {'$exists': False}}],
        }
    )
    if document:
        http_request_event: t_HttpRequestEvent = TypeAdapter(t_HttpRequestEvent).validate_python(document)
        root_http_request = await http_request_event.get_root_http_request()
        await root_http_request.build_events_chain()
    else:
        return

    if recursion_limit > 0:
        await asyncio.sleep(5)
        await group_events(recursion_limit=recursion_limit - 1)
