from core.http.actions.models import HttpRequestModifyActionModel
from core.http.actions.schemas.base_http_action import BaseHttpAction
from core.http.matchers.http_request_matcher import HttpRequestMatcher
from schemas.http_request_modify.http_request import HttpRequestModify


class HttpRequestModifyAction(BaseHttpAction):
    http_request: HttpRequestMatcher
    http_request_modify: HttpRequestModify

    @classmethod
    def from_model(cls, model: HttpRequestModifyActionModel):
        return cls(
            http_request=model.http_request,
            http_request_modify=model.http_request_modify,
            id=model.id,
            priority=model.priority,
            entrypoint=model.entrypoint,
            times=model.times,
            time_to_live=model.time_to_live,
            variables_group=model.variables_group,
        )

    def to_model(self) -> HttpRequestModifyActionModel:
        return HttpRequestModifyActionModel(
            http_request=self.http_request,
            http_request_modify=self.http_request_modify,
            id=self.id,
            priority=self.priority,
            entrypoint=self.entrypoint,
            times=self.times,
            time_to_live=self.time_to_live,
            variables_group=self.variables_group,
        )
