from datetime import datetime
from uuid import UUID

import pytz
from fastapi import APIRouter, Request, Response
from starlette.responses import JSONResponse

from admin.queries import find_event_chains_by_timestamp, get_http_requests_by_timestamp
from admin.schemas import (
    CreateActionResponse,
    EventsChainTimestampPaginatedResponse,
    HttpRequestResponseViewTimestampPaginatedResponse,
)
from core.http.actions.types import t_HttpAction
from core.http.interaction.schemas.http_content import get_data_file_path_by_id
from core.http.matchers.http_request_matcher import HttpRequestMatcher
from mockau_fastapi import MockauFastAPI
from schemas.variables import VariablesContext, VariablesGroup
from utils.compression import detect_and_decompress

admin_router = APIRouter(prefix='/mockau/admin', tags=['Admin'])
admin_debug_router = APIRouter(prefix='/mockau/admin', tags=['Admin Debug'])


@admin_router.post(
    '/create_action',
    response_model=CreateActionResponse,
)
async def create_action(body: t_HttpAction, request: Request):
    app: MockauFastAPI = request.app
    action_model = body.to_model()
    await app.state.clients.mongo_actions_client.insert_one(
        document=action_model.model_dump(mode='json', exclude_none=True),
    )
    await app.state.clients.mongo_actions_client.update_many(
        filters={'id': str(body.id), 'revision': {'$ne': str(action_model.revision)}},
        update={'$set': {'active': False}},
    )

    return Response(
        content=CreateActionResponse(id=body.id).to_json(),
        media_type='application/json',
        status_code=200,
    )


@admin_router.post('/delete_action')
async def delete_action(action_id: UUID, request: Request):
    app: MockauFastAPI = request.app

    result = await app.state.clients.mongo_actions_client.update_one(
        filters={'id': str(action_id)},
        update={'$set': {'active': False}},
    )

    if result.modified_count > 0:
        return Response(
            content={'status': 'ok'},
            media_type='application/json',
            status_code=200,
        )
    else:
        return Response(
            content={'error': 'Not Found'},
            media_type='application/json',
            status_code=404,
        )


@admin_router.post(
    '/create_actions',
)
async def create_actions(body: list[t_HttpAction], request: Request):
    app: MockauFastAPI = request.app

    for action_schema in body:
        action_model = action_schema.to_model()
        await app.state.clients.mongo_actions_client.insert_one(
            document=action_model.model_dump(mode='json', exclude_none=True),
        )
        await app.state.clients.mongo_actions_client.update_many(
            filters={'id': str(action_schema.id), 'revision': {'$ne': str(action_model.revision)}},
            update={'$set': {'active': False}},
        )

    return Response(
        content=CreateActionResponse(id=action_schema.id).to_json(),
        media_type='application/json',
        status_code=200,
    )


@admin_router.post(
    '/get_content/{file_id}/',
)
async def get_content(file_id, decompress: bool = True):
    file_path = get_data_file_path_by_id(file_id)

    if not file_path.exists():
        return JSONResponse(content={'error': 'not found'}, status_code=404)

    with open(file_path, 'rb') as f:
        content = f.read()

    if decompress:
        _, content = detect_and_decompress(content)

    return Response(
        content=content,
        status_code=200,
    )


@admin_router.post(
    '/search_request_responses',
    response_model=HttpRequestResponseViewTimestampPaginatedResponse,
    operation_id='searchRequestResponses',
)
async def search_request_responses(
    request: Request,
    from_: int,
    to: int | None = None,
    limit: int = 10,
    body: HttpRequestMatcher | None = None,
):
    app: MockauFastAPI = request.app

    request_responses = []
    to = to or int(datetime.now(tz=pytz.UTC).timestamp() * 1000000)
    context = VariablesContext(variables_group=VariablesGroup())

    for _ in range(100):
        result = await get_http_requests_by_timestamp(
            clients=app.state.clients,
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
    request: Request,
    from_: int,
    to: int | None = None,
    limit: int = 10,
):
    app: MockauFastAPI = request.app

    to = to or int(datetime.now(tz=pytz.UTC).timestamp() * 1000000)

    events_chains_list = []

    for _ in range(100):
        result = await find_event_chains_by_timestamp(
            clients=app.state.clients,
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
