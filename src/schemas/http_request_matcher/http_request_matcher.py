from typing import Annotated, Optional

from pydantic import Field

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.common_matchers.string_matcher import t_StringMatcher
from schemas.http_request import HttpRequest
from schemas.http_request_matcher.headers import t_HeaderMatcherContainer
from schemas.http_request_matcher.method import t_MethodMatcher
from schemas.http_request_matcher.query_param import t_QueryParamMatcherContainer
from schemas.http_request_matcher.socket_address import SocketAddressMatcher


class HttpRequestMatcher(AbstractMatcher):
    path: Annotated[Optional[t_StringMatcher], Field(default=None, examples=[{'pattern': '/test-env1/.*'}])]
    query_params: Annotated[
        Optional[t_QueryParamMatcherContainer], Field(default=None, examples=[{"key": {"equal_to": "foo"}}])
    ]
    socket_address: Annotated[
        Optional[SocketAddressMatcher],
        Field(default=None, examples=[{'host': {'equal_to': 'mockau.mynetwork.domain'}}]),
    ]
    method: Annotated[Optional[t_MethodMatcher], Field(default=None, examples=[{"any_of": ["GET"]}])]
    headers: Annotated[Optional[t_HeaderMatcherContainer], Field(default=None)]

    # body: Optional[t_Content] = Field(discriminator='type_of')

    def is_matched(self, http_request: HttpRequest) -> bool:
        if self.path and not self.path.is_matched(http_request.path):
            return False
        if self.query_params and not self.query_params.is_matched(http_request.query_params):
            return False
        if self.socket_address and (
            not http_request.socket_address or not self.socket_address.is_matched(http_request.socket_address)
        ):
            return False
        if self.method and not self.method.is_matched(http_request.method):
            return False
        return True
