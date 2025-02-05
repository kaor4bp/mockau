from typing import Generic, Self, TypeVar
from uuid import UUID

from pydantic import computed_field, model_validator

from core.bases.base_schema import BaseSchema
from core.http.events.schemas.events_chain import EventsChain
from schemas.http_request_response_view import HttpRequestResponseView

T_PaginatedItemType = TypeVar('T_PaginatedItemType')


class CreateActionResponse(BaseSchema):
    id: UUID


class TimestampPaginatedResponse(BaseSchema, Generic[T_PaginatedItemType]):
    items: list[T_PaginatedItemType]
    next_timestamp: int | None

    @computed_field
    @property
    def total(self) -> int:
        return len(self.items)


class EventsChainTimestampPaginatedResponse(TimestampPaginatedResponse[EventsChain]):
    @model_validator(mode='after')
    def sort_items(self: Self) -> Self:
        self.items.sort(key=lambda item: item.min_timestamp)
        return self


class HttpRequestResponseViewTimestampPaginatedResponse(TimestampPaginatedResponse[HttpRequestResponseView]):
    @model_validator(mode='after')
    def sort_items(self: Self) -> Self:
        self.items.sort(key=lambda item: item.timestamp)
        return self
