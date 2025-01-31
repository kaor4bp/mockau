from datetime import datetime, timedelta

import pytz
from pydantic import TypeAdapter

from dependencies import mongo_events_client
from models.events import EventTypeGroup, t_Event, t_HttpRequestEvent


async def group_events():
    query = mongo_events_client.find(
        filters={
            'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            '$or': [{'group_id': None}, {'group_id': {'$exists': False}}],
        }
    )
    async for document in query:
        http_request_event: t_HttpRequestEvent = TypeAdapter(t_HttpRequestEvent).validate_python(document)
        root_http_request = await http_request_event.get_root_http_request()
        await root_http_request.build_events_chain()


async def cleanup_events():
    outdated_timestamp = (datetime.now(tz=pytz.UTC) - timedelta(hours=12)).timestamp() * 1000000
    query = mongo_events_client.find(
        filters={
            'timestamp': {'$lte': outdated_timestamp},
            'group_id': {'$ne': None},
        }
    )
    async for document in query:
        event: t_Event = TypeAdapter(t_Event).validate_python(document)
        await mongo_events_client.delete_many({'group_id': str(event.group_id)})
