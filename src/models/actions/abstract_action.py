from uuid import UUID, uuid4

from pydantic import Field

from models.base_model import BaseModel


class AbstractAction(BaseModel):
    id: UUID = Field(default_factory=uuid4)
    priority: int
