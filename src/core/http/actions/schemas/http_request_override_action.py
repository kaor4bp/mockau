from core.http.actions.models import HttpRequestOverrideActionModel
from core.http.actions.schemas.base_http_action import BaseHttpAction
from schemas.http_request_matcher.http_request_matcher import HttpRequestMatcher
from schemas.http_request_override.http_request import HttpRequestOverride


class HttpRequestOverrideAction(BaseHttpAction):
    http_request: HttpRequestMatcher
    http_request_override: HttpRequestOverride

    @classmethod
    def from_model(cls, model: HttpRequestOverrideActionModel):
        return cls(
            http_request=model.http_request,
            http_request_override=model.http_request_override,
            id=model.id,
            priority=model.priority,
            entrypoint=model.entrypoint,
            times=model.times,
            time_to_live=model.time_to_live,
            variables_group=model.variables_group,
        )

    def to_model(self) -> HttpRequestOverrideActionModel:
        return HttpRequestOverrideActionModel(
            http_request=self.http_request,
            http_request_override=self.http_request_override,
            id=self.id,
            priority=self.priority,
            entrypoint=self.entrypoint,
            times=self.times,
            time_to_live=self.time_to_live,
            variables_group=self.variables_group,
        )
