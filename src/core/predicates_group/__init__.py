from typing import Generic, TypeVar, Union

from pydantic import Field

from core.predicates import (
    OrPredicate,
    NotPredicate,
    AndPredicate,
    ObjectContainsSubset,
    ObjectNotContainsSubset,
    ObjectNotEqualTo,
    ObjectEqualTo,
    ObjectHasValue,
    ObjectHasNoValue,
    DynamicKeyMatch,
    NestedArrayContains,
    NestedArrayNotContains,
    NestedArrayEqualTo,
    NestedObjectEqualTo,
    NestedObjectNotEqualTo,
    NestedArrayNotEqualTo,
    NestedObjectNotContainsSubset,
    NestedObjectContainsSubset,
    ArrayNotEqualTo,
    ArrayEqualTo,
    ArrayNotContains,
    ArrayContains,
    t_ScalarStringPredicate,
    t_ScalarIntegerPredicate,
    t_ScalarNumberPredicate,
)
from core.predicates_group.base_predicates_group import BasePredicateGroup

_t_SpecifiedType = TypeVar('_t_SpecifiedType')

__all__ = [
    'BasePredicateGroup',
    't_GenericArrayPredicate',
    't_GenericObjectPredicate',
    't_GenericNestedPredicate',
    't_StringPredicate',
    't_IntegerPredicate',
    't_NumberPredicate',
    #
    'OrPredicate',
    'NotPredicate',
    'AndPredicate',
    'ObjectContainsSubset',
    'ObjectNotContainsSubset',
    'ObjectNotEqualTo',
    'ObjectEqualTo',
    'ObjectHasValue',
    'ObjectHasNoValue',
    'DynamicKeyMatch',
    'NestedArrayContains',
    'NestedArrayNotContains',
    'NestedArrayEqualTo',
    'NestedObjectEqualTo',
    'NestedObjectNotEqualTo',
    'NestedArrayNotEqualTo',
    'NestedObjectNotContainsSubset',
    'NestedObjectContainsSubset',
    'ArrayNotEqualTo',
    'ArrayEqualTo',
    'ArrayNotContains',
    'ArrayContains',
]


class GenericOrPredicate(OrPredicate, Generic[_t_SpecifiedType]):
    predicates: list[_t_SpecifiedType]


class GenericNotPredicate(NotPredicate, Generic[_t_SpecifiedType]):
    predicate: _t_SpecifiedType


class GenericAndPredicate(AndPredicate, Generic[_t_SpecifiedType]):
    predicates: list[_t_SpecifiedType]


type t_StringPredicate = Union[
    t_ScalarStringPredicate,
    GenericOrPredicate['t_StringPredicate'],
    GenericAndPredicate['t_StringPredicate'],
]
type t_IntegerPredicate = Union[
    t_ScalarIntegerPredicate,
    GenericOrPredicate['t_IntegerPredicate'],
    GenericAndPredicate['t_IntegerPredicate'],
]
type t_NumberPredicate = Union[
    t_ScalarNumberPredicate,
    GenericOrPredicate['t_NumberPredicate'],
    GenericAndPredicate['t_NumberPredicate'],
]


class GenericDynamicKeyMatch(DynamicKeyMatch, Generic[_t_SpecifiedType]):
    key: Union[
        t_StringPredicate,
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
