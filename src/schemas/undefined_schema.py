from typing import Literal

from pydantic import Field

from schemas import BaseSchema


class UndefinedSchema(BaseSchema):
    undefined: Literal['$undefined'] = Field(default='$undefined', alias='$undefined')
