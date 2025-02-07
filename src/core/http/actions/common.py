from datetime import timedelta
from enum import Enum

from core.bases.base_schema import BaseSchema


class TimeUnit(Enum):
    SECONDS = 'seconds'
    MINUTES = 'minutes'
    HOURS = 'hours'
    DAYS = 'days'


class Times(BaseSchema):
    remaining_times: int | None = None
    unlimited: bool = False


class TimeToLive(BaseSchema):
    time_to_live: int | None = None
    time_unit: TimeUnit = TimeUnit.SECONDS

    def to_timedelta(self) -> timedelta:
        return timedelta(**{self.time_unit.value: self.time_to_live})
