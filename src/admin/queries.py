from pydantic import TypeAdapter

from dependencies import mongo_events_client
from models.events import EventTypeGroup, t_HttpRequestEvent


async def get_http_requests_by_timestamp(
    from_: int,
    to: int | None,
    limit: int,
) -> list[t_HttpRequestEvent]:
    next_timestamp = to or 0
    timestamp_filter = {'$gte': from_}
    if to:
        timestamp_filter['$lt'] = to
    query = (
        mongo_events_client.find(
            filters={'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST}, 'timestamp': timestamp_filter}
        )
        .sort({'timestamp': 1})
        .limit(limit)
    )

    request_events: list[t_HttpRequestEvent] = [
        TypeAdapter(t_HttpRequestEvent).validate_python(item) for item in await query.to_list()
    ]
    for request_event in request_events:
        if request_event.timestamp > next_timestamp:
            next_timestamp = request_event.timestamp

    query = mongo_events_client.find(
        filters={
            'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            'timestamp': {'$gte': from_, '$lte': next_timestamp},
        }
    ).sort({'timestamp': 1})

    return [TypeAdapter(t_HttpRequestEvent).validate_python(item) for item in await query.to_list()]
