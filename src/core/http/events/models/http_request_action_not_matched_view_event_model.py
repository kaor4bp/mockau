from typing import Literal

from core.http.actions.common import ActionReference
from core.http.events.models.base_http_event_model import BaseHttpEventModel


class HttpRequestActionNotMatchedViewEventModel(BaseHttpEventModel):
    action_reference: ActionReference
    description: str
    level: Literal['INFO'] = 'INFO'
