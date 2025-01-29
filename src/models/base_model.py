from typing import Annotated, Any

from bson import ObjectId
from pydantic import BeforeValidator, Field

from schemas import BaseSchema


def serialize_bson_object_id(value: Any) -> Any:
    if isinstance(value, ObjectId):
        return str(value)
    else:
        return value


class BaseModel(BaseSchema):
    mongo_id: Annotated[str | None, Field(alias='_id', exclude=True), BeforeValidator(serialize_bson_object_id)] = None

    @property
    def mongo_bson_id(self) -> ObjectId | None:
        if self.mongo_id:
            return ObjectId(self.mongo_id)
        else:
            return None

    def to_json_dict(self) -> dict[str, Any]:
        return self.model_dump(mode='json')

    def to_json(self) -> str:
        return self.model_dump_json(indent=2)
