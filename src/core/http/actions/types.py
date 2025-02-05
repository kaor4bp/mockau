from core.http.actions.models import (
    HttpRequestModifyActionModel,
    HttpRequestOverrideActionModel,
    StubHttpResponseActionModel,
)
from core.http.actions.schemas import HttpRequestModifyAction, HttpRequestOverrideAction, StubHttpResponseAction

t_HttpActionModel = HttpRequestModifyActionModel | HttpRequestOverrideActionModel | StubHttpResponseActionModel
t_HttpAction = HttpRequestModifyAction | HttpRequestOverrideAction | StubHttpResponseAction
