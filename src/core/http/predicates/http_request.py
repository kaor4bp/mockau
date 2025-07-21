from typing import Annotated, Optional

from pydantic import Field

from core.http.interaction.common import HttpMethod
from core.http.predicates.body import JsonContentPredicate
from core.http.predicates.headers import HeaderParamItem, t_HeaderParamItemArrayPredicate
from core.http.predicates.method import MethodAnyOfPredicate
from core.http.predicates.query_param import QueryParamItem, t_QueryParamItemArrayPredicate
from core.http.predicates.socket_address import SocketAddressPredicate
from core.predicates import BaseMetaPredicate, StringContains, StringEqualTo, t_ScalarStringPredicate


class HttpRequestPredicate(BaseMetaPredicate):
    path: Annotated[Optional[t_ScalarStringPredicate], Field(default=None)]
    query_params: Annotated[Optional[t_QueryParamItemArrayPredicate], Field(default=None)]
    socket_address: Annotated[
        Optional[SocketAddressPredicate],
        Field(default=None),
    ]
    method: Annotated[Optional[MethodAnyOfPredicate | str], Field(default=None)]
    headers: Annotated[Optional[t_HeaderParamItemArrayPredicate], Field(default=None)]

    body: Optional[JsonContentPredicate] = Field(default=None, discriminator='type_of')


if __name__ == '__main__':
    p1 = HttpRequestPredicate(
        path=StringEqualTo(value='/api/users'),
        method=HttpMethod.GET,
        query_params=[QueryParamItem(key='page', value=StringEqualTo(value='1'))],
        headers=[HeaderParamItem(key='Accept', values=[StringContains(value='json')])],
        body=JsonContentPredicate(body={'hello': 'world!'}),
    )
    p2 = HttpRequestPredicate(path=StringEqualTo(value='/api/users'))

    print(p1.to_yaml_dsl())

    print(p1.compile_predicate().is_subset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_superset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_intersected_with(p2.compile_predicate()))
