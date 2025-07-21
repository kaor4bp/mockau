from types import NoneType
from typing import Union, TYPE_CHECKING, TypeVar, Annotated

from pydantic import Field, model_validator, RootModel

from core.predicates.collections.array_predicates import (
    ArrayNotEqualTo,
    ArrayEqualTo,
    ArrayNotContains,
    ArrayContains,
)
from core.predicates.collections.nested_predicates import (
    NestedArrayContains,
    NestedArrayNotContains,
    NestedArrayEqualTo,
    NestedObjectEqualTo,
    NestedObjectNotEqualTo,
    NestedArrayNotEqualTo,
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
    DynamicKeyMatch,
)
from core.predicates.helpers import deserialize_json_predicate_format
from core.predicates.logical.logical_predicates import (
    AnyPredicate,
    VoidPredicate,
    OrPredicate,
    NotPredicate,
    AndPredicate,
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
    'RootPredicate',
    #
    't_DefaultPredicateType',
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
    'ArrayContains',
    'ArrayNotContains',
    'ArrayNotEqualTo',
    'ArrayEqualTo',
    'ArrayNotContains',
    'ArrayContains',
    # objects
    'DynamicKeyMatch',
    'ObjectContainsSubset',
    'ObjectNotContainsSubset',
    'ObjectNotEqualTo',
    'ObjectEqualTo',
    'ObjectHasValue',
    'ObjectHasNoValue',
    # nested
    'NestedArrayContains',
    'NestedArrayNotContains',
    'NestedArrayEqualTo',
    'NestedObjectEqualTo',
    'NestedObjectNotEqualTo',
    'NestedArrayNotEqualTo',
    'NestedObjectNotContainsSubset',
    'NestedObjectContainsSubset',
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

type t_Py2PredicateType = Union[
    str, int, NoneType, float, list['t_DefaultPredicateType'], dict
]  # bug if dict[str, 't_DefaultPredicateType']
type t_DefaultPredicateType = Union[Annotated['t_Predicate', Field(discriminator='type_of')], t_Py2PredicateType]


# class DynamicKeyMatch(DynamicKeyMatch[t_DefaultPredicateType]):
#     pass
#
#
# class OrPredicate(OrPredicate[t_DefaultPredicateType]):
#     def __invert__(self):
#         return AndPredicate(predicates=[~p for p in self.compiled_value])
#
#
# class AndPredicate(GenericAndPredicate[t_DefaultPredicateType]):
#     def __invert__(self):
#         return OrPredicate(predicates=[~p for p in self.compiled_value])
#
#
# class NotPredicate(NotPredicate[t_DefaultPredicateType]):
#     pass


t_LogicalPredicate = Union[
    OrPredicate,
    AndPredicate,
    AnyPredicate,
    VoidPredicate,
    NotPredicate,
]

_t_SpecifiedType = TypeVar('_t_SpecifiedType')

# t_GenericArrayPredicate = Union[
#     ArrayContains,
#     ArrayNotContains,
#     ArrayEqualTo,
#     ArrayNotEqualTo,
# ]

# t_GenericObjectPredicate = Union[
#     ObjectContainsSubset[_t_SpecifiedType],
#     ObjectNotContainsSubset[_t_SpecifiedType],
#     ObjectNotEqualTo[_t_SpecifiedType],
#     ObjectEqualTo[_t_SpecifiedType],
#     ObjectHasValue[_t_SpecifiedType],
#     ObjectHasNoValue[_t_SpecifiedType],
# ]

# t_GenericNestedPredicate = Union[
#     NestedArrayContains[_t_SpecifiedType],
#     NestedArrayNotContains[_t_SpecifiedType],
#     NestedArrayEqualTo[_t_SpecifiedType],
#     NestedObjectEqualTo[_t_SpecifiedType],
#     NestedObjectNotEqualTo[_t_SpecifiedType],
#     NestedArrayNotEqualTo[_t_SpecifiedType],
#     NestedObjectNotContainsSubset[_t_SpecifiedType],
#     NestedObjectContainsSubset[_t_SpecifiedType],
# ]


# class ArrayContains(ArrayContains[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ArrayNotContains(value=self.value)
#
#
# class ArrayNotContains(ArrayNotContains[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ArrayContains(value=self.value)
#
#
# class ArrayEqualTo(ArrayEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)
#
#
# class ArrayNotEqualTo(ArrayNotEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ArrayEqualTo(value=self.value, ignore_order=self.ignore_order)
#
#
# class ObjectContainsSubset(ObjectContainsSubset[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectNotContainsSubset(value=self.value, dynamic_matches=self.dynamic_matches)
#
#
# class ObjectNotContainsSubset(ObjectNotContainsSubset[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectContainsSubset(value=self.value, dynamic_matches=self.dynamic_matches)
#
#
# class ObjectNotEqualTo(ObjectNotEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectEqualTo(value=self.value, dynamic_matches=self.dynamic_matches)
#
#
# class ObjectEqualTo(ObjectEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectNotEqualTo(value=self.value, dynamic_matches=self.dynamic_matches)
#
#
# class ObjectHasValue(ObjectHasValue[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectHasNoValue(predicate=self.predicate)
#
#
# class ObjectHasNoValue(ObjectHasNoValue[t_DefaultPredicateType]):
#     def __invert__(self):
#         return ObjectHasValue(predicate=self.predicate)
#
#
# class NestedArrayContains(NestedArrayContains[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedArrayNotContains(value=self.value)
#
#
# class NestedArrayNotContains(NestedArrayNotContains[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedArrayContains(value=self.value)
#
#
# class NestedArrayEqualTo(NestedArrayEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)
#
#
# class NestedObjectEqualTo(NestedObjectEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedObjectNotEqualTo(value=self.value)
#
#
# class NestedObjectNotEqualTo(NestedObjectNotEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedObjectEqualTo(value=self.value)
#
#
# class NestedArrayNotEqualTo(NestedArrayNotEqualTo[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedArrayEqualTo(value=self.value, ignore_order=self.ignore_order)
#
#
# class NestedObjectNotContainsSubset(NestedObjectNotContainsSubset[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedObjectContainsSubset(value=self.value)
#
#
# class NestedObjectContainsSubset(NestedObjectContainsSubset[t_DefaultPredicateType]):
#     def __invert__(self):
#         return NestedObjectNotContainsSubset(value=self.value)


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

# t_StringPredicate = Union[
#     t_ScalarStringPredicate,
#     OrPredicate['t_StringPredicate'],
#     GenericAndPredicate['t_StringPredicate'],
# ]
#
# t_IntegerPredicate = Union[
#     t_ScalarIntegerPredicate,
#     OrPredicate['t_IntegerPredicate'],
#     GenericAndPredicate['t_IntegerPredicate'],
# ]

t_UnspecifiedPredicate = TypeVar(
    't_UnspecifiedPredicate',
)


class RootPredicate(RootModel):
    root: t_Predicate = Field(discriminator='type_of')

    @model_validator(mode='before')
    @classmethod
    def json_type_of_deserializer(cls, data):
        return deserialize_json_predicate_format(data)


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
    DynamicKeyMatch.model_rebuild()
    ObjectContainsSubset.model_rebuild()
    ObjectEqualTo.model_rebuild()
    ObjectHasNoValue.model_rebuild()
    ObjectHasValue.model_rebuild()
    ObjectNotContainsSubset.model_rebuild()
    ObjectNotEqualTo.model_rebuild()
