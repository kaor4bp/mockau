from typing import Any

from pydantic import BaseModel, GetJsonSchemaHandler
from pydantic_core import CoreSchema


class BaseSchema(BaseModel):
    def to_json_dict(self) -> dict[str, Any]:
        return self.model_dump(mode='json', exclude_unset=True)

    def to_json(self) -> str:
        return self.model_dump_json(indent=2, exclude_unset=True)

    @classmethod
    def __get_pydantic_json_schema__(cls, schema: CoreSchema, handler: GetJsonSchemaHandler) -> dict[str, Any]:
        """Replace anyOf for Unions to oneOf"""

        json_schema = handler(schema)
        json_schema = handler.resolve_ref_schema(json_schema)
        if json_schema.get('properties'):
            for k, v in json_schema['properties'].items():
                if v.get('anyOf'):
                    v['oneOf'] = v.pop('anyOf')
                if v.get('items') and v['items'].get('anyOf'):
                    v['items']['oneOf'] = v['items'].pop('anyOf')

        return json_schema
