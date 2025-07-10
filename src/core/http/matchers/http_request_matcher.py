from typing import Annotated, Optional

from pydantic import Field

from core.deprecated_matchers.abstract_matcher import AbstractMatcher
from core.deprecated_matchers.string_matcher import t_StringMatcher
from core.http.interaction.schemas import HttpRequest
from core.http.matchers.headers import t_HeaderMatcherContainer
from core.http.matchers.method import t_MethodMatcher
from core.http.matchers.query_param import t_QueryParamMatcherContainer
from core.http.matchers.socket_address import SocketAddressMatcher
from core.predicates.base_predicate import t_Predicate
from core.predicates.collections.object_predicates import ObjectEqualTo
from schemas.variables import VariablesContext, variables_context_transaction


class HttpRequestMatcher(AbstractMatcher):
    path: Annotated[Optional[t_StringMatcher], Field(default=None, examples=[{'set_variable': '/test-env1/.*'}])]
    query_params: Annotated[
        Optional[t_QueryParamMatcherContainer], Field(default=None, examples=[{"key": {"equal_to": "foo"}}])
    ]
    socket_address: Annotated[
        Optional[SocketAddressMatcher],
        Field(default=None, examples=[{'socket_address': {'equal_to': 'mockau.mynetwork.domain'}}]),
    ]
    method: Annotated[Optional[t_MethodMatcher], Field(default=None, examples=[{"any_of": ["GET"]}])]
    headers: Annotated[Optional[t_HeaderMatcherContainer], Field(default=None)]

    # body: Optional[t_Content] = Field(discriminator='type_of')

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        object_plain_matcher = {}
        if self.path:
            object_plain_matcher['path'] = self.path.to_predicate(context=context)
        if self.query_params:
            object_plain_matcher['query_params'] = self.query_params.to_predicate(context=context)
        if self.socket_address:
            object_plain_matcher['socket_address'] = self.socket_address.to_predicate(context=context)
        if self.method:
            object_plain_matcher['method'] = self.method.to_predicate(context=context)
        if self.headers:
            object_plain_matcher['headers'] = self.headers.to_predicate(context=context)
        return ObjectEqualTo(value=object_plain_matcher)

    @variables_context_transaction
    def is_matched(self, http_request: HttpRequest, *, context: VariablesContext) -> bool:
        if self.path and not self.path.is_matched(http_request.path, context=context):
            return False
        if self.query_params and not self.query_params.is_matched(http_request.query_params, context=context):
            return False
        if self.socket_address and (
            not http_request.socket_address
            or not self.socket_address.is_matched(http_request.socket_address, context=context)
        ):
            return False
        if self.method and not self.method.is_matched(http_request.method, context=context):
            return False
        return True
