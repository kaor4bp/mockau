from fastapi import APIRouter, Response
from pydantic import TypeAdapter
from starlette.responses import JSONResponse

from admin.queries import get_http_requests_by_timestamp
from admin.schemas import (
    ChainsOfEventsListViewResponse,
    CreateActionResponse,
    HttpRequestResponsesListViewResponse,
    HttpRequestResponseViewResponse,
)
from dependencies import mongo_actions_manager, mongo_events_manager
from schemas.actions import t_Action
from schemas.events import EventType, EventTypeGroup, t_HttpRequestEvent
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher

admin_router = APIRouter(prefix='/mockau/admin', tags=['Admin'])


@admin_router.post('/create_action')
async def create_action(action: t_Action):
    await mongo_actions_manager.update_one(
        filters={'id': str(action.id)}, update={'$set': action.model_dump(mode='json')}, upsert=True
    )

    return Response(
        content=CreateActionResponse(id=action.id).model_dump_json(indent=2),
        media_type='application/json',
        status_code=200,
    )


@admin_router.get('/get_last_events_chain')
async def get_last_events_chain():
    query = (
        mongo_events_manager.find(
            filters={
                'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            }
        )
        .sort({'timestamp': -1})
        .limit(1)
    )
    last_request = await query.to_list()
    if not last_request:
        return JSONResponse(content=[], status_code=404)
    last_request_event: t_HttpRequestEvent = TypeAdapter(t_HttpRequestEvent).validate_python(last_request[0])
    last_request_event = await last_request_event.get_root_http_request()

    chain_of_events = await last_request_event.build_events_chain()
    return JSONResponse(content=chain_of_events.model_dump(mode='json'), status_code=200)


@admin_router.get('/get_last_request_response')
async def get_last_request_response():
    query = (
        mongo_events_manager.find(
            filters={
                'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            }
        )
        .sort({'timestamp': -1})
        .limit(1)
    )
    last_request = await query.to_list()
    if not last_request:
        return JSONResponse(content={'error': 'not found'}, status_code=404)
    last_request_event: t_HttpRequestEvent = TypeAdapter(t_HttpRequestEvent).validate_python(last_request[0])
    http_response_event = await last_request_event.get_http_response_event()
    return JSONResponse(
        content=HttpRequestResponseViewResponse(
            request=last_request_event.http_request, response=http_response_event.http_response
        ).model_dump(mode='json'),
        status_code=200,
    )


@admin_router.post(
    '/search_request_responses',
    response_model=HttpRequestResponsesListViewResponse,
    operation_id='searchRequestResponses',
)
async def search_request_responses(
    body: HttpRequestMatcher,
    from_: int,
    to: int | None = None,
    limit: int = 10,
):
    response = HttpRequestResponsesListViewResponse(
        items=[],
        next_timestamp=None,
    )
    no_next_events = False

    while True:
        new_items = []
        request_events = await get_http_requests_by_timestamp(
            from_=from_,
            to=to,
            limit=max(limit - len(response.items), 1),
        )
        if not request_events:
            no_next_events = True
            break

        for request_event in request_events:
            if not body.is_matched(request_event.http_request):
                continue
            http_response_event = await request_event.get_http_response_event()
            new_items.append(
                HttpRequestResponseViewResponse(
                    request=request_event.http_request,
                    response=http_response_event.http_response,
                )
            )

        if len(response.items) + len(new_items) <= limit:
            response.items += new_items
            if response.items:
                response.next_timestamp = max([event.timestamp for event in request_events]) + 1
            elif to is not None:
                response.next_timestamp = to
            from_ = response.next_timestamp
        else:
            break

    if no_next_events:
        response.next_timestamp = None

    return JSONResponse(content=response.model_dump(mode='json'), status_code=200)


@admin_router.get('/get_events_chain', operation_id='getEventsChain')
async def get_events_chain(from_: int, to: int | None = None, limit: int = 10, is_final_only: bool = True):
    timestamp_filter = {'$gte': from_}
    if to:
        timestamp_filter['$lt'] = to

    query = (
        mongo_events_manager.find(
            filters={'type_of': EventType.HTTP_EXTERNAL_REQUEST.value, 'timestamp': timestamp_filter}
        )
        .sort({'timestamp': 1})
        .limit(limit=limit)
    )
    requests = await query.to_list()
    if not requests:
        return JSONResponse(content=[], status_code=404)

    request_events: list[t_HttpRequestEvent] = [
        TypeAdapter(t_HttpRequestEvent).validate_python(request) for request in requests
    ]
    request_events.sort(key=lambda e: e.timestamp)
    query = mongo_events_manager.find(
        filters={
            'type_of': {'$in': EventTypeGroup.INBOUND_HTTP_REQUEST},
            'timestamp': {'$gte': request_events[0].timestamp, '$lte': request_events[-1].timestamp},
        }
    ).sort({'timestamp': 1})
    next_timestamp = request_events[-1].timestamp + 1
    requests = await query.to_list()

    request_events: list[t_HttpRequestEvent] = [
        TypeAdapter(t_HttpRequestEvent).validate_python(request) for request in requests
    ]
    root_events: list[t_HttpRequestEvent] = [await event.get_root_http_request() for event in request_events]
    root_events = [event for event in root_events if event.timestamp >= from_ and (to is None or event.timestamp < to)]

    root_events.sort(key=lambda e: e.timestamp)

    if not root_events:
        return JSONResponse(content=[], status_code=404)

    chains = []
    processed_root_events = []
    for root_event in root_events:
        if root_event.http_request.id in processed_root_events:
            continue
        processed_root_events.append(root_event.http_request.id)

        events_chain = await root_event.build_events_chain()
        if (
            events_chain.from_timestamp >= from_
            and (to is None or events_chain.to_timestamp < to)
            and (not is_final_only or events_chain.is_final)
        ):
            chains.append(events_chain)

    return JSONResponse(
        content=ChainsOfEventsListViewResponse(items=chains, next_timestamp=next_timestamp).model_dump(mode='json'),
        status_code=200,
    )
