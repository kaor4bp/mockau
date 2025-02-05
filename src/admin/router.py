from datetime import datetime

import pytz
from fastapi import APIRouter, Response
from starlette.responses import JSONResponse

from admin.queries import find_event_chains_by_timestamp, get_http_requests_by_timestamp
from admin.schemas import (
    CreateActionResponse,
    EventsChainTimestampPaginatedResponse,
    HttpRequestResponseViewTimestampPaginatedResponse,
)
from core.http.actions.types import t_HttpAction
from dependencies import mongo_actions_client
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher
from schemas.variables import VariablesContext, VariablesGroup

admin_router = APIRouter(prefix='/mockau/admin', tags=['Admin'])
admin_debug_router = APIRouter(prefix='/mockau/admin', tags=['Admin Debug'])


@admin_router.post(
    '/create_action',
    response_model=CreateActionResponse,
)
async def create_action(body: t_HttpAction):
    await mongo_actions_client.update_one(
        filters={'id': str(body.id)}, update={'$set': body.to_model().to_json_dict()}, upsert=True
    )

    return Response(
        content=CreateActionResponse(id=body.id).to_json(),
        media_type='application/json',
        status_code=200,
    )


@admin_router.post(
    '/search_request_responses',
    response_model=HttpRequestResponseViewTimestampPaginatedResponse,
    operation_id='searchRequestResponses',
)
async def search_request_responses(
    from_: int,
    to: int | None = None,
    limit: int = 10,
    body: HttpRequestMatcher | None = None,
):
    request_responses = []
    to = to or int(datetime.now(tz=pytz.UTC).timestamp() * 1000000)
    context = VariablesContext(variables_group=VariablesGroup())

    for _ in range(100):
        result = await get_http_requests_by_timestamp(
            from_=from_,
            to=to,
            limit=limit - len(request_responses),
        )
        new_request_responses = []
        for request_response in result.items:
            if not body or body.is_matched(request_response.http_request, context=context):
                new_request_responses.append(request_response)

        from_ = result.next_timestamp
        if not result.items or from_ is None:
            break
        request_responses += new_request_responses
        if len(request_responses) >= limit:
            break

    if from_ == to:
        from_ = None

    return JSONResponse(
        content=HttpRequestResponseViewTimestampPaginatedResponse(
            items=request_responses,
            next_timestamp=from_,
        ).to_json_dict(),
    )


@admin_router.get('/get_events_chain', operation_id='getEventsChain')
async def get_events_chain(
    from_: int,
    to: int | None = None,
    limit: int = 10,
):
    to = to or int(datetime.now(tz=pytz.UTC).timestamp() * 1000000)

    events_chains_list = []

    for _ in range(100):
        result = await find_event_chains_by_timestamp(
            from_=from_,
            to=to,
            limit=limit,
        )
        events_chains_list += result.items
        from_ = result.next_timestamp
        if len(events_chains_list) >= limit:
            break
        if not result.items or from_ is None:
            break

    if from_ == to:
        from_ = None

    return JSONResponse(
        content=EventsChainTimestampPaginatedResponse(
            items=events_chains_list,
            next_timestamp=from_,
        ).to_json_dict()
    )
