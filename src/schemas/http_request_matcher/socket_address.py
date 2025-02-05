from typing import Optional

from core.http.interaction.schemas import HttpSocketAddress
from schemas.matchers.abstract_matcher import AbstractMatcher
from schemas.matchers.integer_matcher import t_IntegerMatcher
from schemas.matchers.string_matcher import t_StringMatcher
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
