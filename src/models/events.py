from datetime import datetime
from enum import Enum
from typing import Literal, Optional
from uuid import UUID, uuid4

import pytz
from bson import ObjectId
from pydantic import Field, TypeAdapter, computed_field

from dependencies import mongo_events_client
from models.base_model import BaseModel
from schemas import HttpRequest
from schemas.http_response import HttpResponse


class EventType(Enum):
    HTTP_INTERNAL_REQUEST = 'http_internal_request'
    HTTP_EXTERNAL_REQUEST = 'http_external_request'
    HTTP_TRANSIT_REQUEST = 'http_transit_request'
    HTTP_REQUEST_ACTION_MATCHED = 'http_request_action_matched'
    HTTP_REQUEST_ACTIONS_MISMATCHED = 'http_request_actions_mismatched'

    HTTP_RECEIVED_RESPONSE = 'http_received_response'


class EventTypeGroup:
    ALL_HTTP_REQUEST = [
        EventType.HTTP_EXTERNAL_REQUEST.value,
        EventType.HTTP_INTERNAL_REQUEST.value,
        EventType.HTTP_TRANSIT_REQUEST.value,
    ]
    INBOUND_HTTP_REQUEST = [
        EventType.HTTP_EXTERNAL_REQUEST.value,
        EventType.HTTP_TRANSIT_REQUEST.value,
    ]


class ChainOfEvents(BaseModel):
    events: list['t_Event | ChainOfEvents']

    @property
    def all_events(self) -> list['t_Event']:
        events = []
        for event in self.events:
            if isinstance(event, ChainOfEvents):
                events += event.all_events
            else:
                events.append(event)
        return sorted(events, key=lambda e: e.timestamp)

    @computed_field
    @property
    def has_response(self) -> bool:
        return any(isinstance(event, EventReceivedHttpResponse) for event in self.events)

    @computed_field
    @property
    def has_actions_mismatched(self) -> bool:
        return any(isinstance(event, EventHttpRequestActionsMismatched) for event in self.events)

    @computed_field
    @property
    def is_initiated_by_external_request(self) -> bool:
        return any(isinstance(event, EventExternalHttpRequest) for event in self.events)

    @computed_field
    @property
    def is_final(self) -> bool:
        for event in self.events:
            if isinstance(event, ChainOfEvents) and not event.is_final:
                return False
        return self.has_response or self.has_actions_mismatched

    @computed_field
    @property
    def duration(self) -> float:
        if len(self.all_events) < 2:
            return 0
        else:
            return (self.all_events[-1].created_at - self.all_events[0].created_at).total_seconds()

    @computed_field
    @property
    def total(self) -> int:
        return len(self.all_events)

    @property
    def from_timestamp(self) -> int:
        if self.events:
            return int(self.all_events[0].created_at.timestamp() * 1000000)
        return 0

    @property
    def to_timestamp(self) -> int:
        if self.events:
            return int(self.all_events[-1].created_at.timestamp() * 1000000)
        else:
            return 0


class BaseEvent(BaseModel):
    type_of: EventType
    # id: UUID = Field(default_factory=uuid4)
    created_at: datetime = Field(default_factory=lambda: datetime.now(tz=pytz.UTC))
    group_id: UUID | None = None
    parent_group_id: UUID | None = None

    @computed_field
    @property
    def timestamp(self) -> int:
        return int(self.created_at.timestamp() * 1000000)

    async def send_to_mongo(self) -> None:
        await mongo_events_client.insert_one(self.to_json_dict())


class BaseHttpRequestEvent(BaseEvent):
    http_request: HttpRequest
    track_http_request_id: UUID | None = None

    async def _get_tracked_http_request(self) -> Optional['t_HttpRequestEvent']:
        if not self.track_http_request_id:
            return None

        query_result = await mongo_events_client.find_one(
            filters={
                'track_http_request_id': str(self.track_http_request_id),
                'http_request.id': {'$ne': str(self.track_http_request_id)},
            }
        )
        if not query_result:
            return None
        event = TypeAdapter(t_HttpRequestEvent).validate_python(query_result)
        if event.http_request.id != self.track_http_request_id:
            return event

    async def _get_child_http_request(self) -> Optional['t_HttpRequestEvent']:
        query_result = await mongo_events_client.find_one(
            filters={
                'parent_http_request_id': str(self.http_request.id),
            }
        )
        if not query_result:
            return None
        return TypeAdapter(t_HttpRequestEvent).validate_python(query_result)

    async def _get_parent_http_request(self) -> Optional['t_HttpRequestEvent']:
        if not self.track_http_request_id:
            return None

        query_result = await mongo_events_client.find_one(filters={'http_request.id': str(self.track_http_request_id)})
        if not query_result:
            return None
        return TypeAdapter(t_HttpRequestEvent).validate_python(query_result)

    async def _get_sub_events(self) -> list['t_HttpRequestSubEvent']:
        query = mongo_events_client.find(filters={'http_request_id': str(self.http_request.id)}).sort({'timestamp': 1})
        return [TypeAdapter(t_HttpRequestSubEvent).validate_python(e) for e in await query.to_list()]

    async def get_http_response_event(
        self,
        recursive: bool = True,
        prefer_external_response: bool = False,
    ) -> Optional['EventReceivedHttpResponse']:
        query_result = await mongo_events_client.find_one(
            filters={
                'http_request_id': str(self.http_request.id),
                'type_of': EventType.HTTP_RECEIVED_RESPONSE.value,
            }
        )

        if query_result:
            return TypeAdapter(EventReceivedHttpResponse).validate_python(query_result)
        if not recursive:
            return None

        children_http_request = await self._get_child_http_request()
        if not children_http_request:
            return None

        if prefer_external_response:
            tracked_request = await children_http_request._get_tracked_http_request()
            if tracked_request:
                tracked_response = await tracked_request.get_http_response_event(recursive=recursive)
                if tracked_response:
                    return tracked_response

        return await children_http_request.get_http_response_event(recursive=recursive)

    async def get_root_http_request(self) -> 't_HttpRequestEvent':
        http_request = self

        for _ in range(100):
            parent_http_request = await http_request._get_parent_http_request()
            if parent_http_request:
                http_request = parent_http_request
            else:
                break
        else:
            raise AssertionError('Too many recursions')
        return http_request

    async def build_events_chain(self, parent_group_id: UUID | None = None) -> ChainOfEvents:
        events = []
        group_id = self.group_id or uuid4()

        events.append(self)
        events += await self._get_sub_events()

        children_http_request = await self._get_child_http_request()
        if children_http_request:
            events.append(children_http_request)
            tracked_http_request = await children_http_request._get_tracked_http_request()
            if tracked_http_request:
                tracked_chain_of_events = await tracked_http_request.build_events_chain(parent_group_id=group_id)
                events.append(tracked_chain_of_events)
            events += await children_http_request._get_sub_events()

        chain_of_events = ChainOfEvents(events=events)

        if chain_of_events.is_final:
            for event in events:
                event.group_id = group_id
                event.parent_group_id = parent_group_id
            await mongo_events_client.update_many(
                filters={'$or': [{'_id': ObjectId(event.mongo_id)} for event in events]},
                update={
                    '$set': {
                        'group_id': str(group_id),
                        'parent_group_id': str(self.parent_group_id) if self.parent_group_id else None,
                    }
                },
            )
        return chain_of_events


class BaseHttpRequestSubEvent(BaseEvent):
    http_request_id: UUID


class EventExternalHttpRequest(BaseHttpRequestEvent):
    type_of: Literal['http_external_request'] = 'http_external_request'


class EventTransitHttpRequest(BaseHttpRequestEvent):
    type_of: Literal['http_transit_request'] = 'http_transit_request'
    track_http_request_id: UUID


class EventInternalHttpRequest(BaseHttpRequestEvent):
    type_of: Literal['http_internal_request'] = 'http_internal_request'
    track_http_request_id: UUID
    parent_http_request_id: UUID

    async def _get_parent_http_request(self) -> Optional['t_HttpRequestEvent']:
        query_result = await mongo_events_client.find_one(
            filters={
                'http_request.id': str(self.parent_http_request_id),
            }
        )
        if not query_result:
            return None
        return TypeAdapter(t_HttpRequestEvent).validate_python(query_result)


class EventHttpRequestActionMatched(BaseHttpRequestSubEvent):
    type_of: Literal['http_request_action_matched'] = 'http_request_action_matched'
    action_id: UUID


class EventHttpRequestActionsMismatched(BaseHttpRequestSubEvent):
    type_of: Literal['http_request_actions_mismatched'] = 'http_request_actions_mismatched'


class EventReceivedHttpResponse(BaseHttpRequestSubEvent):
    type_of: Literal['http_received_response'] = 'http_received_response'
    http_response: HttpResponse


t_HttpRequestEvent = EventExternalHttpRequest | EventTransitHttpRequest | EventInternalHttpRequest
t_HttpRequestSubEvent = EventHttpRequestActionMatched | EventHttpRequestActionsMismatched | EventReceivedHttpResponse
t_Event = t_HttpRequestEvent | t_HttpRequestSubEvent
