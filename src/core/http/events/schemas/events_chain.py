from typing import Self

from elasticsearch_dsl import Q
from pydantic import model_validator

from core.bases.base_schema import BaseSchema
from core.http.events.common import HttpEventType, HttpEventTypeGroup
from core.http.events.documents import (
    HttpRequestActionEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestEventDocument,
    HttpRequestResponseViewEventDocument,
    HttpResponseEventDocument,
)
from core.http.events.models import HttpRequestEventModel
from core.http.events.types import t_EventModel
from dependencies import elasticsearch_client
from schemas.http_request_response_view import HttpRequestResponseView


class EventsChain(BaseSchema):
    events: list[t_EventModel]

    @model_validator(mode='after')
    def sort_items(self: Self) -> Self:
        self.events.sort(key=lambda item: item.created_at)
        return self

    @property
    def min_timestamp(self) -> int | None:
        min_timestamp = None
        for event in self.events:
            event_timestamp = int(event.created_at.timestamp() * 1000000)
            if not min_timestamp or event_timestamp < min_timestamp:
                min_timestamp = event_timestamp
        return min_timestamp

    def _get_http_response_event(self, http_request_event: HttpRequestEventModel):
        all_request_events = (
            event for event in self.events if event.event.value in HttpEventTypeGroup.ALL_HTTP_REQUEST
        )
        response_events = (event for event in self.events if event.event is HttpEventType.HTTP_RECEIVED_RESPONSE)

        for response_event in response_events:
            if http_request_event.mockau_traceparent == response_event.mockau_traceparent:
                return response_event

        child_event = None
        for sub_request_event in all_request_events:
            if sub_request_event.parent_mockau_traceparent == http_request_event.mockau_traceparent:
                child_event = sub_request_event
                break
        if child_event:
            return self._get_http_response_event(child_event)

    def get_http_request_response_views(self) -> list[HttpRequestResponseView]:
        request_events = [
            event for event in self.events if event.event.value in HttpEventTypeGroup.INBOUND_HTTP_REQUEST
        ]
        results = []
        for request_event in request_events:
            http_response_event = self._get_http_response_event(request_event)
            results.append(
                HttpRequestResponseView(
                    http_request=request_event.http_request,
                    http_response=http_response_event.http_response if http_response_event else None,
                    timestamp=int(request_event.created_at.timestamp() * 1000000),
                )
            )
        return results

    @classmethod
    async def create_by_trace_id(cls, trace_id: str) -> 'EventsChain':
        event_models = []
        document_types = [
            HttpRequestResponseViewEventDocument,
            HttpResponseEventDocument,
            HttpRequestActionEventDocument,
            HttpRequestErrorEventDocument,
            HttpRequestEventDocument,
        ]
        for document_type in document_types:
            query = Q(
                "bool",
                must=[Q("term", mockau_trace_id=trace_id)],
                must_not=[Q("term", event=HttpEventType.HTTP_REQUEST_RESPONSE_VIEW.value)],
            )

            response = await document_type.search(using=elasticsearch_client).query(query).execute()

            for hit in response.hits:
                event_models.append(hit.to_model())
        event_models.sort(key=lambda event: event.created_at)
        return cls(events=event_models)

    @classmethod
    async def bulk_create_by_trace_ids(cls, trace_ids: list[str]) -> 'list[EventsChain]':
        event_models = {}
        document_types = [
            HttpRequestResponseViewEventDocument,
            HttpResponseEventDocument,
            HttpRequestActionEventDocument,
            HttpRequestErrorEventDocument,
            HttpRequestEventDocument,
        ]
        for document_type in document_types:
            query = Q(
                "bool",
                should=[Q("term", mockau_trace_id=trace_id) for trace_id in trace_ids],
                must_not=[Q("term", event=HttpEventType.HTTP_REQUEST_RESPONSE_VIEW.value)],
            )

            response = await document_type.search(using=elasticsearch_client).query(query).execute()

            for hit in response.hits:
                event_models.setdefault(hit.mockau_trace_id, []).append(hit.to_model())
        chains = []
        for events in event_models.values():
            events.sort(key=lambda event: event.created_at)
            chains.append(cls(events=events))

        return chains
