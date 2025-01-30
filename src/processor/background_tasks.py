from datetime import datetime, timedelta

import pytz
from fastapi import BackgroundTasks
from pydantic import TypeAdapter

from dependencies import mongo_events_client
from models.events import EventTypeGroup, t_Event, t_HttpRequestEvent


async def group_events():
    for _ in range(5):
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
            break


async def cleanup_events():
    outdated_timestamp = (datetime.now(tz=pytz.UTC) - timedelta(hours=12)).timestamp() * 1000000
    query = mongo_events_client.find(
        filters={
            'timestamp': {'$lte': outdated_timestamp},
            'group_id': {'$ne': None},
        }
    ).batch_size(10)
    async for document in query:
        event: t_Event = TypeAdapter(t_Event).validate_python(document)
        await mongo_events_client.delete_many({'group_id': str(event.group_id)})


async def schedule_background_tasks(background_tasks: BackgroundTasks):
    background_tasks.add_task(group_events)
    background_tasks.add_task(cleanup_events)
