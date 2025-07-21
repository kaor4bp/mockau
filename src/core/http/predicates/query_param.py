from typing import Optional, TypeAliasType

from pydantic import Field

from core.predicates import (
    BaseMetaPredicate,
    GenericArrayContains,
    GenericArrayEqualTo,
    t_GenericArrayPredicate,
    t_StringPredicateType,
)


class QueryParamItem(BaseMetaPredicate):
    key: t_StringPredicateType
    value: Optional[t_StringPredicateType] = Field(default=None)


t_QueryParamItemArrayPredicate = TypeAliasType(
    't_QueryParamItemArrayPredicate', t_GenericArrayPredicate, type_params=(QueryParamItem,)
)


class QueryParamItems(BaseMetaPredicate):
    query_params: t_QueryParamItemArrayPredicate


if __name__ == '__main__':
    p1 = QueryParamItems(query_params=GenericArrayContains[QueryParamItem](value=[QueryParamItem(key='foo')]))
    p2 = QueryParamItems(query_params=GenericArrayEqualTo[QueryParamItem](value=[QueryParamItem(key='foo')]))

    print(p1.compile_predicate().is_subset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_superset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_intersected_with(p2.compile_predicate()))

    # x = p2.model_dump_json(indent=2, exclude=None, by_alias=True)
    # print(x)
    # print(QueryParamItems.model_validate_json(x))
