from types import NoneType
from typing import Union, TYPE_CHECKING

from core.predicates.collections.array_predicates import (
    ArrayNotStrictEqualTo,
    ArrayStrictEqualTo,
    ArrayNotEqualToWithoutOrder,
    ArrayNotContains,
    ArrayContains,
    ArrayEqualToWithoutOrder,
)
from core.predicates.collections.nested_predicates import (
    NestedArrayContains,
    NestedArrayNotContains,
    NestedArrayStrictEqualTo,
    NestedObjectEqualTo,
    NestedObjectNotEqualTo,
    NestedArrayNotStrictEqualTo,
    NestedObjectNotContainsSubset,
    NestedObjectContainsSubset,
)
from core.predicates.collections.object_predicates import (
    ObjectContainsSubset,
    ObjectNotContainsSubset,
    ObjectNotEqualTo,
    ObjectEqualTo,
    ObjectHasValue,
    ObjectHasNoValue,
)
from core.predicates.logical.logical_predicates import (
    OrPredicate,
    AndPredicate,
    AnyPredicate,
    VoidPredicate,
    NotPredicate,
)
from core.predicates.scalars.boolean_predicates import (
    BooleanEqualTo,
)
from core.predicates.scalars.integer_predicates import (
    IntegerLessThan,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerGreaterOrEqualThan,
    IntegerNotEqualTo,
    IntegerLessOrEqualThan,
)
from core.predicates.scalars.null_predicates import (
    OptionalPredicate,
    IsNull,
)
from core.predicates.scalars.number_predicates import (
    NumberEqualTo,
    NumberLessThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberGreaterOrEqualThan,
    NumberNotEqualTo,
)
from core.predicates.scalars.string_predicates import (
    StringPattern,
    StringEqualTo,
    StringContains,
    StringNotEqualTo,
    StringNotPattern,
    StringNotContains,
)

__all__ = [
    't_Py2PredicateType',
    't_BooleanPredicate',
    't_IntegerPredicate',
    't_NumberPredicate',
    't_StringPredicate',
    't_ScalarPredicate',
    't_LogicalPredicate',
    't_ArrayPredicate',
    't_ObjectPredicate',
    't_NestedPredicate',
    't_CollectionPredicate',
    't_Predicate',
    # integer
    'IntegerLessThan',
    'IntegerEqualTo',
    'IntegerGreaterThan',
    'IntegerLessOrEqualThan',
    'IntegerGreaterOrEqualThan',
    'IntegerNotEqualTo',
    'IntegerLessOrEqualThan',
    # boolean
    'OptionalPredicate',
    'IsNull',
    # string
    'StringPattern',
    'StringEqualTo',
    'StringContains',
    'StringNotEqualTo',
    'StringNotPattern',
    'StringNotContains',
    # number
    'NumberEqualTo',
    'NumberLessThan',
    'NumberGreaterThan',
    'NumberLessOrEqualThan',
    'NumberGreaterOrEqualThan',
    'NumberNotEqualTo',
    # logical
    'OrPredicate',
    'AndPredicate',
    'AnyPredicate',
    'VoidPredicate',
    'NotPredicate',
    # arrays
    'ArrayContains',
    'ArrayNotContains',
    'ArrayNotStrictEqualTo',
    'ArrayStrictEqualTo',
    'ArrayNotEqualToWithoutOrder',
    'ArrayNotEqualToWithoutOrder',
    'ArrayNotContains',
    'ArrayContains',
    'ArrayEqualToWithoutOrder',
    # objects
    'ObjectContainsSubset',
    'ObjectNotContainsSubset',
    'ObjectNotEqualTo',
    'ObjectEqualTo',
    'ObjectHasValue',
    'ObjectHasNoValue',
    # nested
    'NestedArrayContains',
    'NestedArrayNotContains',
    'NestedArrayStrictEqualTo',
    'NestedObjectEqualTo',
    'NestedObjectNotEqualTo',
    'NestedArrayNotStrictEqualTo',
    'NestedObjectNotContainsSubset',
    'NestedObjectContainsSubset',
]


t_BooleanPredicate = Union[BooleanEqualTo, IsNull]
t_IntegerPredicate = Union[
    IntegerLessThan,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerGreaterOrEqualThan,
    IntegerNotEqualTo,
]
t_NumberPredicate = Union[
    NumberEqualTo,
    NumberLessThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberGreaterOrEqualThan,
    NumberNotEqualTo,
]
t_StringPredicate = Union[
    StringPattern,
    StringEqualTo,
    StringContains,
    StringNotEqualTo,
    StringNotPattern,
    StringNotContains,
]
t_ScalarPredicate = Union[
    t_BooleanPredicate,
    t_IntegerPredicate,
    t_NumberPredicate,
    t_StringPredicate,
]

t_LogicalPredicate = Union[
    OrPredicate,
    AndPredicate,
    AnyPredicate,
    VoidPredicate,
    NotPredicate,
]

t_ArrayPredicate = Union[
    ArrayContains,
    ArrayNotContains,
    ArrayStrictEqualTo,
    ArrayNotStrictEqualTo,
    ArrayEqualToWithoutOrder,
    ArrayNotEqualToWithoutOrder,
]

t_ObjectPredicate = Union[
    ObjectContainsSubset,
    ObjectNotContainsSubset,
    ObjectNotEqualTo,
    ObjectEqualTo,
    ObjectHasValue,
    ObjectHasNoValue,
]

t_NestedPredicate = Union[
    NestedArrayContains,
    NestedArrayNotContains,
    NestedArrayStrictEqualTo,
    NestedObjectEqualTo,
    NestedObjectNotEqualTo,
    NestedArrayNotStrictEqualTo,
    NestedObjectNotContainsSubset,
    NestedObjectContainsSubset,
]

t_CollectionPredicate = Union[
    t_ArrayPredicate,
    t_ObjectPredicate,
    t_NestedPredicate,
]

t_Predicate = Union[t_ScalarPredicate, t_LogicalPredicate, t_CollectionPredicate]

t_Py2PredicateType = Union[str, int, NoneType, float, list, dict]


if not TYPE_CHECKING:
    # scalars
    OptionalPredicate.model_rebuild()

    # logical
    AndPredicate.model_rebuild()
    OrPredicate.model_rebuild()
    NotPredicate.model_rebuild()

    # arrays
    ArrayContains.model_rebuild()
    ArrayEqualToWithoutOrder.model_rebuild()
    ArrayNotContains.model_rebuild()
    ArrayNotEqualToWithoutOrder.model_rebuild()
    ArrayNotStrictEqualTo.model_rebuild()
    ArrayStrictEqualTo.model_rebuild()

    # nested
    NestedArrayContains.model_rebuild()
    NestedArrayNotContains.model_rebuild()
    NestedArrayNotStrictEqualTo.model_rebuild()
    NestedArrayStrictEqualTo.model_rebuild()
    NestedObjectContainsSubset.model_rebuild()
    NestedObjectEqualTo.model_rebuild()
    NestedObjectNotContainsSubset.model_rebuild()
    NestedObjectNotEqualTo.model_rebuild()

    # objects
    ObjectContainsSubset.model_rebuild()
    ObjectEqualTo.model_rebuild()
    ObjectHasNoValue.model_rebuild()
    ObjectHasValue.model_rebuild()
    ObjectNotContainsSubset.model_rebuild()
    ObjectNotEqualTo.model_rebuild()
