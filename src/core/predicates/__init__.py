from types import NoneType
from typing import Union, TYPE_CHECKING, TypeVar, Annotated

from pydantic import Field, model_validator, RootModel

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
    GenericDynamicKeyMatch,
)
from core.predicates.helpers import deserialize_json_predicate_format
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
    'RootPredicate',
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
    'DynamicKeyMatch',
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

type t_Py2PredicateType = Union[
    str, int, NoneType, float, list['t_DefaultPredicateType'], dict
]  # bug if dict[str, 't_DefaultPredicateType']
type t_DefaultPredicateType = Union[Annotated['t_Predicate', Field(discriminator='type_of')], t_Py2PredicateType]


class DynamicKeyMatch(GenericDynamicKeyMatch[t_DefaultPredicateType]):
    pass


class OrPredicate(GenericOrPredicate[t_DefaultPredicateType]):
    def __invert__(self):
        return AndPredicate(predicates=[~p for p in self.compiled_value])


class AndPredicate(GenericAndPredicate[t_DefaultPredicateType]):
    def __invert__(self):
        return OrPredicate(predicates=[~p for p in self.compiled_value])


class NotPredicate(GenericNotPredicate[t_DefaultPredicateType]):
    pass


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


class ArrayContains(GenericArrayContains[t_DefaultPredicateType]):
    def __invert__(self):
        return ArrayNotContains(value=self.value)


class ArrayNotContains(GenericArrayNotContains[t_DefaultPredicateType]):
    def __invert__(self):
        return ArrayContains(value=self.value)


class ArrayEqualTo(GenericArrayEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return ArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)


class ArrayNotEqualTo(GenericArrayNotEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return ArrayEqualTo(value=self.value, ignore_order=self.ignore_order)


class ObjectContainsSubset(GenericObjectContainsSubset[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectNotContainsSubset(value=self.value, dynamic_matches=self.dynamic_matches)


class ObjectNotContainsSubset(GenericObjectNotContainsSubset[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectContainsSubset(value=self.value, dynamic_matches=self.dynamic_matches)


class ObjectNotEqualTo(GenericObjectNotEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectEqualTo(value=self.value, dynamic_matches=self.dynamic_matches)


class ObjectEqualTo(GenericObjectEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectNotEqualTo(value=self.value, dynamic_matches=self.dynamic_matches)


class ObjectHasValue(GenericObjectHasValue[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectHasNoValue(predicate=self.predicate)


class ObjectHasNoValue(GenericObjectHasNoValue[t_DefaultPredicateType]):
    def __invert__(self):
        return ObjectHasValue(predicate=self.predicate)


class NestedArrayContains(GenericNestedArrayContains[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedArrayNotContains(value=self.value)


class NestedArrayNotContains(GenericNestedArrayNotContains[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedArrayContains(value=self.value)


class NestedArrayEqualTo(GenericNestedArrayEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedArrayNotEqualTo(value=self.value, ignore_order=self.ignore_order)


class NestedObjectEqualTo(GenericNestedObjectEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedObjectNotEqualTo(value=self.value)


class NestedObjectNotEqualTo(GenericNestedObjectNotEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedObjectEqualTo(value=self.value)


class NestedArrayNotEqualTo(GenericNestedArrayNotEqualTo[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedArrayEqualTo(value=self.value, ignore_order=self.ignore_order)


class NestedObjectNotContainsSubset(GenericNestedObjectNotContainsSubset[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedObjectContainsSubset(value=self.value)


class NestedObjectContainsSubset(GenericNestedObjectContainsSubset[t_DefaultPredicateType]):
    def __invert__(self):
        return NestedObjectNotContainsSubset(value=self.value)


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
