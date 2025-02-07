from typing import Union

from core.plain_matchers.common_plain_matchers import And, Any, Not, Or
from core.plain_matchers.integer_plain_matchers import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
)
from core.plain_matchers.object_plain_matchers import ObjectPlainMatcher
from core.plain_matchers.string_plain_matchers import StringContains, StringEqualTo, StringPattern

t_PlainMatcher = Union[
    Any,
    Not,
    And,
    Or,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerGreaterOrEqualThan,
    IntegerLessThan,
    IntegerLessOrEqualThan,
    StringEqualTo,
    StringPattern,
    StringContains,
    ObjectPlainMatcher,
]
