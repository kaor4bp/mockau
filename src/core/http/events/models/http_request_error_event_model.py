from typing import Literal

from core.http.events.models.base_http_event_model import BaseHttpEventModel


class HttpRequestErrorEventModel(BaseHttpEventModel):
    level: Literal['ERROR'] = 'ERROR'
