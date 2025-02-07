from typing import Annotated, Union

from pydantic import Field

from core.plain_matchers.integer_plain_matchers import (
    IntegerAnd,
    IntegerAny,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNot,
    IntegerOr,
)
from core.plain_matchers.object_plain_matchers import ObjectAnd, ObjectAny, ObjectNot, ObjectOr, ObjectPlainMatcher
from core.plain_matchers.string_plain_matchers import (
    StringAnd,
    StringAny,
    StringContains,
    StringEqualTo,
    StringNot,
    StringOr,
    StringPattern,
)

t_IntegerPlainMatcher = Annotated[
    Union[
        IntegerEqualTo,
        IntegerGreaterThan,
        IntegerGreaterOrEqualThan,
        IntegerLessThan,
        IntegerLessOrEqualThan,
        IntegerAny,
        IntegerNot,
        IntegerAnd,
        IntegerOr,
    ],
    Field(discriminator='type_of'),
]

t_StringPlainMatcher = Annotated[
    Union[
        StringEqualTo,
        StringPattern,
        StringContains,
        StringAny,
        StringNot,
        StringAnd,
        StringOr,
    ],
    Field(discriminator='type_of'),
]

t_ObjectPlainMatcher = Annotated[
    Union[
        ObjectPlainMatcher,
        ObjectAny,
        ObjectNot,
        ObjectAnd,
        ObjectOr,
    ],
    Field(discriminator='type_of'),
]

t_PlainMatcher = Annotated[
    Union[
        IntegerEqualTo,
        IntegerGreaterThan,
        IntegerGreaterOrEqualThan,
        IntegerLessThan,
        IntegerLessOrEqualThan,
        IntegerAny,
        IntegerNot,
        IntegerAnd,
        IntegerOr,
        StringEqualTo,
        StringPattern,
        StringContains,
        StringAny,
        StringNot,
        StringAnd,
        StringOr,
        ObjectPlainMatcher,
        ObjectAny,
        ObjectNot,
        ObjectAnd,
        ObjectOr,
    ],
    Field(discriminator='type_of'),
]
