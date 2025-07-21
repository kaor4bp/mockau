from typing import Optional

from pydantic import Field

from core.predicates import t_StringPredicateType
from core.predicates.base_predicate import BaseMetaPredicate


class SocketAddressPredicate(BaseMetaPredicate):
    host: Optional[t_StringPredicateType] = Field(default=None)
    port: Optional[t_StringPredicateType] = Field(default=None)
    scheme: Optional[t_StringPredicateType] = Field(default=None)
