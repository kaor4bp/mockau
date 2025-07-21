from typing import Optional, TypeAliasType

from pydantic import Field

from core.predicates import (
    GenericArrayContains,
    GenericArrayEqualTo,
    t_GenericArrayPredicate,
    t_StringArrayPredicateType,
    t_StringPredicateType,
)
from core.predicates.base_predicate import BaseMetaPredicate


class HeaderParamItem(BaseMetaPredicate):
    key: t_StringPredicateType
    values: Optional[t_StringArrayPredicateType] = Field(default=None)


t_HeaderParamItemArrayPredicate = TypeAliasType(
    't_HeaderParamItemArrayPredicate',
    t_GenericArrayPredicate,
    type_params=(HeaderParamItem,),
)


class HeaderParams(BaseMetaPredicate):
    headers: t_HeaderParamItemArrayPredicate


if __name__ == '__main__':
    p1 = HeaderParams(headers=GenericArrayContains[HeaderParamItem](value=[HeaderParamItem(key='foo')]))
    p2 = HeaderParams(headers=GenericArrayEqualTo[HeaderParamItem](value=[HeaderParamItem(key='foo')]))

    print(p1.compile_predicate().is_subset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_superset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_intersected_with(p2.compile_predicate()))
