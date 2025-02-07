from core.http.actions.models.base_http_action_model import BaseHttpActionModel
from schemas.http_request_modify.http_request import HttpRequestModify


class HttpRequestModifyActionModel(BaseHttpActionModel):
    http_request_modify: HttpRequestModify
