from typing import Optional

from core.deprecated_matchers.abstract_matcher import AbstractMatcher
from core.deprecated_matchers.integer_matcher import t_IntegerMatcher
from core.deprecated_matchers.string_matcher import t_StringMatcher
from core.http.interaction.schemas import HttpSocketAddress
from core.predicates.base_predicate import t_Predicate
from core.predicates.collections.object_predicates import ObjectEqualTo
from schemas.variables import VariablesContext, variables_context_transaction


class SocketAddressMatcher(AbstractMatcher):
    host: Optional[t_StringMatcher] = None
    port: Optional[t_IntegerMatcher] = None
    scheme: Optional[t_StringMatcher] = None

    @variables_context_transaction
    def is_matched(self, socket_address: HttpSocketAddress, *, context: VariablesContext) -> bool:
        if self.host and not self.host.is_matched(socket_address.host, context=context):
            return False
        if self.port and not self.port.is_matched(socket_address.port, context=context):
            return False
        if self.scheme and not self.scheme.is_matched(socket_address.scheme, context=context):
            return False
        return True

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        object_plain_matcher = {}
        if self.host:
            object_plain_matcher['host'] = self.host.to_predicate(context=context)
        if self.port:
            object_plain_matcher['port'] = self.port.to_predicate(context=context)
        if self.scheme:
            object_plain_matcher['scheme'] = self.scheme.to_predicate(context=context)
        return ObjectEqualTo(value=object_plain_matcher)
