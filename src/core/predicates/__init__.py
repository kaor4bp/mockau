from types import NoneType
from typing import Annotated, Generic
from typing import TypeVar, Union, TYPE_CHECKING, TypeAliasType

from pydantic import Field, model_validator, RootModel

from core.predicates.base_predicate import BaseMetaPredicate
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
    StringInList,
    StringNotInList,
    StringConcatEqualTo,
    StringConcatNotEqualTo,
)

__all__ = [
    'RootPredicate',
    'BaseMetaPredicate',
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
    'StringConcatEqualTo',
    'StringConcatNotEqualTo',
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
    # aliases
    't_StringPredicateType',
    't_IntegerPredicateType',
    't_StringOrIntegerPredicateType',
    't_NumberPredicateType',
    't_GenericArrayPredicate',
    't_GenericObjectPredicate',
    't_GenericNestedPredicate',
    # Generics
    'GenericNotPredicate',
    'GenericOrPredicate',
    'GenericAndPredicate',
    'GenericArrayContains',
    'GenericArrayNotContains',
    'GenericArrayEqualTo',
    'GenericArrayNotEqualTo',
    'GenericObjectContainsSubset',
    'GenericObjectNotContainsSubset',
    'GenericObjectNotEqualTo',
    'GenericObjectEqualTo',
    'GenericObjectHasValue',
    'GenericObjectHasNoValue',
    'GenericDynamicKeyMatch',
    #
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
    StringInList,
    StringNotInList,
    StringConcatEqualTo,
    StringConcatNotEqualTo,
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


class RootPredicate(RootModel):
    root: t_Predicate = Field(discriminator='type_of')

    @model_validator(mode='before')
    @classmethod
    def json_type_of_deserializer(cls, data):
        return deserialize_json_predicate_format(data)


# region Generics and aliases
_t_SpecifiedType = TypeVar('_t_SpecifiedType')


class GenericOrPredicate(OrPredicate, Generic[_t_SpecifiedType]):
    predicates: list[_t_SpecifiedType]


class GenericNotPredicate(NotPredicate, Generic[_t_SpecifiedType]):
    predicate: _t_SpecifiedType


class GenericAndPredicate(AndPredicate, Generic[_t_SpecifiedType]):
    predicates: list[_t_SpecifiedType]


class GenericDynamicKeyMatch(DynamicKeyMatch, Generic[_t_SpecifiedType]):
    key: Union[
        't_StringPredicateType',
        str,
    ] = Field(alias='$key')
    value: _t_SpecifiedType = Field(alias='$value')


class GenericObjectContainsSubset(ObjectContainsSubset, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericObjectNotContainsSubset(ObjectNotContainsSubset, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericObjectNotEqualTo(ObjectNotEqualTo, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericObjectEqualTo(ObjectEqualTo, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericObjectHasValue(ObjectHasValue, Generic[_t_SpecifiedType]):
    predicate: _t_SpecifiedType


class GenericObjectHasNoValue(ObjectHasNoValue, Generic[_t_SpecifiedType]):
    predicate: _t_SpecifiedType


class GenericNestedArrayContains(NestedArrayContains, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedArrayNotContains(NestedArrayNotContains, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedArrayEqualTo(NestedArrayEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedObjectEqualTo(NestedObjectEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedObjectNotEqualTo(NestedObjectNotEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedArrayNotEqualTo(NestedArrayNotEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericNestedObjectNotContainsSubset(NestedObjectNotContainsSubset, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericNestedObjectContainsSubset(NestedObjectContainsSubset, Generic[_t_SpecifiedType]):
    value: dict[str, _t_SpecifiedType] = Field(default_factory=dict)
    dynamic_matches: list[GenericDynamicKeyMatch[_t_SpecifiedType]] = Field(default_factory=list)


class GenericArrayNotEqualTo(ArrayNotEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericArrayEqualTo(ArrayEqualTo, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericArrayNotContains(ArrayNotContains, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


class GenericArrayContains(ArrayContains, Generic[_t_SpecifiedType]):
    value: list['_t_SpecifiedType']


type t_StringPredicateType = Union[
    t_ScalarStringPredicate,
    GenericOrPredicate['t_StringPredicateType'],
    GenericAndPredicate['t_StringPredicateType'],
    str,
]
type t_IntegerPredicateType = Union[
    t_ScalarIntegerPredicate,
    GenericOrPredicate['t_IntegerPredicateType'],
    GenericAndPredicate['t_IntegerPredicateType'],
    int,
]
type t_StringOrIntegerPredicateType = Union[
    t_ScalarIntegerPredicate,
    t_ScalarStringPredicate,
    GenericOrPredicate['t_StringOrIntegerPredicateType'],
    GenericAndPredicate['t_StringOrIntegerPredicateType'],
    int,
    str,
]
type t_NumberPredicateType = Union[
    t_ScalarNumberPredicate,
    GenericOrPredicate['t_NumberPredicateType'],
    GenericAndPredicate['t_NumberPredicateType'],
    float,
]


type t_GenericArrayPredicate = Union[
    GenericArrayContains, GenericArrayNotContains, GenericArrayEqualTo, GenericArrayNotEqualTo, list
]

t_GenericObjectPredicate = Union[
    GenericObjectContainsSubset[_t_SpecifiedType],
    GenericObjectNotContainsSubset[_t_SpecifiedType],
    GenericObjectNotEqualTo[_t_SpecifiedType],
    GenericObjectEqualTo[_t_SpecifiedType],
    GenericObjectHasValue[_t_SpecifiedType],
    GenericObjectHasNoValue[_t_SpecifiedType],
    dict[t_StringPredicateType, _t_SpecifiedType],
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
    list[_t_SpecifiedType],
    dict[t_StringPredicateType, _t_SpecifiedType],
]

type t_StringArrayPredicateType = TypeAliasType(
    't_StringArrayPredicateType',
    Union[t_GenericArrayPredicate],
    type_params=(t_StringPredicateType,),
)

# endregion

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

    # string list predicates
    StringInList.model_rebuild()
    StringNotInList.model_rebuild()

    # string concatenation predicates
    StringConcatEqualTo.model_rebuild()
    StringConcatNotEqualTo.model_rebuild()
