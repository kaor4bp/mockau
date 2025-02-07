from typing import Optional

from core.http.interaction.schemas import HttpSocketAddress
from core.matchers.abstract_matcher import AbstractMatcher
from core.matchers.integer_matcher import t_IntegerMatcher
from core.matchers.string_matcher import t_StringMatcher
from core.plain_matchers.object_plain_matchers import ObjectPlainMatcher
from core.plain_matchers.types import t_PlainMatcher
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

    def to_plain_matcher(self, *, context: VariablesContext) -> t_PlainMatcher:
        object_plain_matcher = {}
        if self.host:
            object_plain_matcher['host'] = self.host.to_plain_matcher(context=context)
        if self.port:
            object_plain_matcher['port'] = self.port.to_plain_matcher(context=context)
        if self.scheme:
            object_plain_matcher['scheme'] = self.scheme.to_plain_matcher(context=context)
        return ObjectPlainMatcher(
            obj=object_plain_matcher,
            obj_name=f'{self.__class__.__module__}#{self.__class__.__name__}',
        )
