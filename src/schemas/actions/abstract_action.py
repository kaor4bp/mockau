from uuid import UUID, uuid4

from pydantic import Field

from schemas import BaseSchema


class AbstractAction(BaseSchema):
    id: UUID = Field(default_factory=uuid4)
    priority: int
