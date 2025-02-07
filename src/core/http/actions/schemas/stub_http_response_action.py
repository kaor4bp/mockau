from core.http.actions.models import StubHttpResponseActionModel
from core.http.actions.schemas.base_http_action import BaseHttpAction
from core.http.interaction.schemas.http_response import HttpResponse
from core.http.matchers.http_request_matcher import HttpRequestMatcher


class StubHttpResponseAction(BaseHttpAction):
    http_request: HttpRequestMatcher
    http_response: HttpResponse

    @classmethod
    def from_model(cls, model: StubHttpResponseActionModel):
        return cls(
            http_request=model.http_request,
            http_response=model.http_response,
            id=model.id,
            priority=model.priority,
            entrypoint=model.entrypoint,
            times=model.times,
            time_to_live=model.time_to_live,
            variables_group=model.variables_group,
        )

    def to_model(self) -> StubHttpResponseActionModel:
        return StubHttpResponseActionModel(
            http_request=self.http_request,
            http_response=self.http_response,
            id=self.id,
            priority=self.priority,
            entrypoint=self.entrypoint,
            times=self.times,
            time_to_live=self.time_to_live,
            variables_group=self.variables_group,
        )
