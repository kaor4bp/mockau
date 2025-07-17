from types import NoneType
from typing import Union, TYPE_CHECKING, TypeVar, Annotated

from pydantic import Field

from core.predicates.collections.array_predicates import (
    GenericArrayNotEqualTo,
    GenericArrayEqualTo,
    GenericArrayNotContains,
    GenericArrayContains,
)
from core.predicates.collections.nested_predicates import (
    GenericNestedArrayContains,
    GenericNestedArrayNotContains,
    GenericNestedArrayEqualTo,
    GenericNestedObjectEqualTo,
    GenericNestedObjectNotEqualTo,
    GenericNestedArrayNotEqualTo,
    GenericNestedObjectNotContainsSubset,
    GenericNestedObjectContainsSubset,
)
from core.predicates.collections.object_predicates import (
    GenericObjectContainsSubset,
    GenericObjectNotContainsSubset,
    GenericObjectNotEqualTo,
    GenericObjectEqualTo,
    GenericObjectHasValue,
    GenericObjectHasNoValue,
)
from core.predicates.logical.logical_predicates import (
    AnyPredicate,
    VoidPredicate,
    GenericOrPredicate,
    GenericAndPredicate,
    GenericNotPredicate,
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
    #
    't_Py2PredicateType',
    't_ScalarBooleanPredicate',
    't_ScalarIntegerPredicate',
    't_ScalarNumberPredicate',
    't_ScalarStringPredicate',
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
    'GenericArrayContains',
    'GenericArrayNotContains',
    'GenericArrayNotEqualTo',
    'GenericArrayEqualTo',
    'GenericArrayNotContains',
    'GenericArrayContains',
    # objects
    'GenericObjectContainsSubset',
    'GenericObjectNotContainsSubset',
    'GenericObjectNotEqualTo',
    'GenericObjectEqualTo',
    'GenericObjectHasValue',
    'GenericObjectHasNoValue',
    # nested
    'GenericNestedArrayContains',
    'GenericNestedArrayNotContains',
    'GenericNestedArrayEqualTo',
    'GenericNestedObjectEqualTo',
    'GenericNestedObjectNotEqualTo',
    'GenericNestedArrayNotEqualTo',
    'GenericNestedObjectNotContainsSubset',
    'GenericNestedObjectContainsSubset',
]


t_ScalarBooleanPredicate = Union[BooleanEqualTo, IsNull]
t_ScalarIntegerPredicate = Union[
    IntegerLessThan,
    IntegerEqualTo,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerGreaterOrEqualThan,
    IntegerNotEqualTo,
]
t_ScalarNumberPredicate = Union[
    NumberEqualTo,
    NumberLessThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberGreaterOrEqualThan,
    NumberNotEqualTo,
]
t_ScalarStringPredicate = Union[
    StringPattern,
    StringEqualTo,
    StringContains,
    StringNotEqualTo,
    StringNotPattern,
    StringNotContains,
]
t_ScalarPredicate = Union[
    t_ScalarBooleanPredicate,
    t_ScalarIntegerPredicate,
    t_ScalarNumberPredicate,
    t_ScalarStringPredicate,
]

_t_DefaultPredicateType = Union[Annotated['t_Predicate', Field(discriminator='type_of')], 't_Py2PredicateType']

OrPredicate = GenericOrPredicate[_t_DefaultPredicateType]
AndPredicate = GenericAndPredicate[_t_DefaultPredicateType]
NotPredicate = GenericNotPredicate[_t_DefaultPredicateType]

t_LogicalPredicate = Union[
    OrPredicate,
    AndPredicate,
    AnyPredicate,
    VoidPredicate,
    NotPredicate,
]

_t_SpecifiedType = TypeVar('_t_SpecifiedType')

t_GenericArrayPredicate = Union[
    GenericArrayContains,
    GenericArrayNotContains,
    GenericArrayEqualTo,
    GenericArrayNotEqualTo,
]

t_GenericObjectPredicate = Union[
    GenericObjectContainsSubset[_t_SpecifiedType],
    GenericObjectNotContainsSubset[_t_SpecifiedType],
    GenericObjectNotEqualTo[_t_SpecifiedType],
    GenericObjectEqualTo[_t_SpecifiedType],
    GenericObjectHasValue[_t_SpecifiedType],
    GenericObjectHasNoValue[_t_SpecifiedType],
]

t_GenericNestedPredicate = Union[
    GenericNestedArrayContains[_t_SpecifiedType],
    GenericNestedArrayNotContains[_t_SpecifiedType],
    GenericNestedArrayEqualTo[_t_SpecifiedType],
    GenericNestedObjectEqualTo[_t_SpecifiedType],
    GenericNestedObjectNotEqualTo[_t_SpecifiedType],
    GenericNestedArrayNotEqualTo[_t_SpecifiedType],
    GenericNestedObjectNotContainsSubset[_t_SpecifiedType],
    GenericNestedObjectContainsSubset[_t_SpecifiedType],
]

ArrayContains = GenericArrayContains[_t_DefaultPredicateType]
ArrayNotContains = GenericArrayNotContains[_t_DefaultPredicateType]
ArrayEqualTo = GenericArrayEqualTo[_t_DefaultPredicateType]
ArrayNotEqualTo = GenericArrayNotEqualTo[_t_DefaultPredicateType]

ObjectContainsSubset = GenericObjectContainsSubset[_t_DefaultPredicateType]
ObjectNotContainsSubset = GenericObjectNotContainsSubset[_t_DefaultPredicateType]
ObjectNotEqualTo = GenericObjectNotEqualTo[_t_DefaultPredicateType]
ObjectEqualTo = GenericObjectEqualTo[_t_DefaultPredicateType]
ObjectHasValue = GenericObjectHasValue[_t_DefaultPredicateType]
ObjectHasNoValue = GenericObjectHasNoValue[_t_DefaultPredicateType]

NestedArrayContains = GenericNestedArrayContains[_t_DefaultPredicateType]
NestedArrayNotContains = GenericNestedArrayNotContains[_t_DefaultPredicateType]
NestedArrayEqualTo = GenericNestedArrayEqualTo[_t_DefaultPredicateType]
NestedObjectEqualTo = GenericNestedObjectEqualTo[_t_DefaultPredicateType]
NestedObjectNotEqualTo = GenericNestedObjectNotEqualTo[_t_DefaultPredicateType]
NestedArrayNotEqualTo = GenericNestedArrayNotEqualTo[_t_DefaultPredicateType]
NestedObjectNotContainsSubset = GenericNestedObjectNotContainsSubset[_t_DefaultPredicateType]
NestedObjectContainsSubset = GenericNestedObjectContainsSubset[_t_DefaultPredicateType]

t_ArrayPredicate = Union[
    ArrayContains,
    ArrayNotContains,
    ArrayEqualTo,
    ArrayNotEqualTo,
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
    NestedArrayEqualTo,
    NestedObjectEqualTo,
    NestedObjectNotEqualTo,
    NestedArrayNotEqualTo,
    NestedObjectNotContainsSubset,
    NestedObjectContainsSubset,
]

t_CollectionPredicate = Union[
    t_ArrayPredicate,
    t_ObjectPredicate,
    t_NestedPredicate,
]

t_Predicate = Annotated[
    Union[t_ScalarPredicate, t_LogicalPredicate, t_CollectionPredicate],
    Field(discriminator='type_of'),
]

t_Py2PredicateType = Union[str, int, NoneType, float, list, dict]

t_StringPredicate = Union[
    t_ScalarStringPredicate,
    GenericOrPredicate['t_StringPredicate'],
    GenericAndPredicate['t_StringPredicate'],
]

t_IntegerPredicate = Union[
    t_ScalarIntegerPredicate,
    GenericOrPredicate['t_IntegerPredicate'],
    GenericAndPredicate['t_IntegerPredicate'],
]


t_UnspecifiedPredicate = TypeVar(
    't_UnspecifiedPredicate',
)


if not TYPE_CHECKING:
    # scalars
    OptionalPredicate.model_rebuild()

    # logical
    AndPredicate.model_rebuild()
    OrPredicate.model_rebuild()
    NotPredicate.model_rebuild()

    # arrays
    ArrayContains.model_rebuild()
    ArrayNotContains.model_rebuild()
    ArrayNotEqualTo.model_rebuild()
    ArrayEqualTo.model_rebuild()

    # nested
    NestedArrayContains.model_rebuild()
    NestedArrayNotContains.model_rebuild()
    NestedArrayNotEqualTo.model_rebuild()
    NestedArrayEqualTo.model_rebuild()
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
