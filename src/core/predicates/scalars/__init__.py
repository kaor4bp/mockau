from typing import Union

from core.predicates.scalars.boolean_predicates import (
    BooleanEqualTo,
)
from core.predicates.scalars.integer_predicates import (
    IntegerLessThan,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerGreaterOrEqualThan,
)
from core.predicates.scalars.number_predicates import (
    NumberEqualTo,
    NumberLessThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberGreaterOrEqualThan,
)
from core.predicates.scalars.string_predicates import (
    StringPattern,
    StringEqualTo,
    StringContains,
)

t_BooleanPredicate = Union[BooleanEqualTo,]
t_IntegerPredicate = Union[
    IntegerLessThan,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerGreaterOrEqualThan,
]
t_NumberPredicate = Union[
    NumberEqualTo,
    NumberLessThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberGreaterOrEqualThan,
]
t_StringPredicate = Union[
    StringPattern,
    StringEqualTo,
    StringContains,
]
t_ScalarPredicate = Union[
    t_BooleanPredicate,
    t_IntegerPredicate,
    t_NumberPredicate,
    t_StringPredicate,
]
