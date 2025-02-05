from typing import Literal

from pydantic import Field

from core.bases.base_schema import BaseSchema


class UndefinedSchema(BaseSchema):
    undefined: Literal['$undefined'] = Field(default='$undefined', alias='$undefined')
