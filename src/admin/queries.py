from uuid import UUID

from elasticsearch_dsl import A
from minow_fastapi import MockauSharedClients

from admin.schemas import EventsChainTimestampPaginatedResponse, HttpRequestResponseViewTimestampPaginatedResponse
from core.http.actions.common import ActionReference
from core.http.events.common import HttpEventType
from core.http.events.documents import HttpRequestActionEventDocument
from core.http.events.documents.http_request_event_document import HttpRequestEventDocument
from core.http.events.models import HttpRequestEventModel
from core.http.events.schemas.events_chain import EventsChain
from schemas.http_request_response_view import HttpRequestResponseView


async def get_http_requests_by_timestamp(
    clients: MockauSharedClients,
    from_: int,
    to: int,
    limit: int,
) -> HttpRequestResponseViewTimestampPaginatedResponse:
    search = (
        HttpRequestEventDocument.search(using=clients.elasticsearch_client)
        .sort('created_at')
        .filter("range", timestamp={'gte': from_, 'lt': to})
        .filter(
            "terms",
            event=[
                HttpEventType.HTTP_EXTERNAL_REQUEST.value,
                HttpEventType.HTTP_TRANSIT_REQUEST.value,
            ],
        )
        .extra(size=limit)
    )
    response = await search.execute()
    max_timestamp = None
    for document in response.hits:
        if not max_timestamp or document.timestamp > max_timestamp:
            max_timestamp = document.timestamp
    if not max_timestamp:
        return HttpRequestResponseViewTimestampPaginatedResponse(
            items=[],
            next_timestamp=None,
        )

    search = (
        HttpRequestEventDocument.search(using=clients.elasticsearch_client)
        .sort('created_at')
        .filter("range", timestamp={'gte': from_, 'lte': max_timestamp})
        .filter(
            "terms",
            event=[
                HttpEventType.HTTP_EXTERNAL_REQUEST.value,
                HttpEventType.HTTP_TRANSIT_REQUEST.value,
            ],
        )
    )
    response = await search.execute()

    request_events_list: list[HttpRequestEventModel] = []
    minow_trace_ids_list = []
    for document in response.hits:
        minow_trace_ids_list.append(document.minow_trace_id)
        request_events_list.append(document.to_model())

    events_chains_list = await EventsChain.bulk_create_by_trace_ids(
        clients=clients,
        trace_ids=list(set(minow_trace_ids_list)),
    )
    results = []

    for events_chain in events_chains_list:
        for request_response_view in events_chain.get_http_request_response_views():
            for request_event_index, request_event in enumerate(request_events_list):
                if request_event.minow_traceparent == request_response_view.http_request.minow_traceparent:
                    results.append(request_response_view)
                    request_events_list.pop(request_event_index)
                    break

    search = HttpRequestActionEventDocument.search(using=clients.elasticsearch_client).filter(
        "terms",
        minow_traceparent=[request_event.minow_traceparent for request_event in request_events_list],
    )
    response = await search.execute()

    missed_action_events: list[HttpRequestActionEventDocument] = [document.to_model() for document in response.hits]

    for request_event in request_events_list:
        found_action_event = None
        for missed_action_event in missed_action_events:
            if missed_action_event.minow_traceparent == request_event.minow_traceparent:
                found_action_event = missed_action_event
                break
        results.append(
            HttpRequestResponseView(
                http_request=request_event.http_request,
                http_response=None,
                action_reference=(
                    ActionReference(
                        action_id=UUID(found_action_event.action_id),
                        action_revision=UUID(found_action_event.action_revision),
                    )
                    if found_action_event
                    else None
                ),
                timestamp=int(request_event.created_at.timestamp() * 1000000),
            )
        )

    return HttpRequestResponseViewTimestampPaginatedResponse(
        items=results,
        next_timestamp=max_timestamp + 1 if max_timestamp else None,
    )


async def find_event_chains_by_timestamp(
    clients: MockauSharedClients,
    from_: int,
    to: int,
    limit: int,
) -> EventsChainTimestampPaginatedResponse:
    search = (
        HttpRequestEventDocument.search(using=clients.elasticsearch_client)
        .sort('created_at')
        .filter("range", timestamp={'gte': from_, 'lt': to})
        .filter(
            "terms",
            event=[
                HttpEventType.HTTP_EXTERNAL_REQUEST.value,
                HttpEventType.HTTP_TRANSIT_REQUEST.value,
            ],
        )
        .extra(size=limit)
    )
    response = await search.execute()
    max_timestamp = None
    for document in response.hits:
        if not max_timestamp or document.timestamp > max_timestamp:
            max_timestamp = document.timestamp
    if not max_timestamp:
        return EventsChainTimestampPaginatedResponse(
            items=[],
            next_timestamp=None,
        )

    search = (
        HttpRequestEventDocument.search(using=clients.elasticsearch_client)
        .sort('created_at')
        .filter("range", timestamp={'gte': from_, 'lte': max_timestamp})
        .filter(
            "terms",
            event=[
                HttpEventType.HTTP_EXTERNAL_REQUEST.value,
                HttpEventType.HTTP_TRANSIT_REQUEST.value,
            ],
        )
    )

    agg = A("terms", field="minow_trace_id", size=limit)
    search.aggs.bucket("unique_minow_trace_ids", agg)
    response = await search.execute()
    unique_minow_trace_ids = [bucket.key for bucket in response.aggregations.unique_minow_trace_ids.buckets]

    events_chains = await EventsChain.bulk_create_by_trace_ids(clients=clients, trace_ids=unique_minow_trace_ids)

    return EventsChainTimestampPaginatedResponse(
        items=events_chains,
        next_timestamp=max_timestamp + 1 if max_timestamp else None,
    )
