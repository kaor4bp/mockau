from typing import Generic
from uuid import UUID

from black.nodes import TypeVar
from pydantic import computed_field

from models.events import ChainOfEvents
from schemas import BaseSchema, HttpRequest
from schemas.http_response import HttpResponse

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


class ChainsOfEventsListViewResponse(TimestampPaginatedResponse[ChainOfEvents]):
    pass


class HttpRequestResponseViewResponse(BaseSchema):
    request: HttpRequest
    response: HttpResponse | None


class HttpRequestResponsesListViewResponse(TimestampPaginatedResponse[HttpRequestResponseViewResponse]):
    pass
