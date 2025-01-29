from typing import Optional

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.common_matchers.integer_matcher import t_IntegerMatcher
from schemas.common_matchers.string_matcher import t_StringMatcher
from schemas.http_request.http_parts import HttpRequestSocketAddress


class SocketAddressMatcher(AbstractMatcher):
    host: Optional[t_StringMatcher] = None
    port: Optional[t_IntegerMatcher] = None
    scheme: Optional[t_StringMatcher] = None

    def is_matched(self, socket_address: HttpRequestSocketAddress) -> bool:
        if self.host and not self.host.is_matched(socket_address.host):
            return False
        if self.port and not self.port.is_matched(socket_address.port):
            return False
        if self.scheme and not self.scheme.is_matched(socket_address.scheme):
            return False
        return True
