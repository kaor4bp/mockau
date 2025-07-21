from typing import Literal

from core.http.interaction.common import HttpContentType
from core.predicates import StringContains, t_DefaultPredicateType
from core.predicates.base_predicate import BaseMetaPredicate


class JsonContentPredicate(BaseMetaPredicate):
    type_of: Literal[HttpContentType.JSON] = HttpContentType.JSON
    body: t_DefaultPredicateType


if __name__ == '__main__':
    p1 = JsonContentPredicate(body=StringContains(value='hello'))
    p2 = JsonContentPredicate(body=StringContains(value='world'))

    print(p1.compile_predicate().is_subset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_superset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_intersected_with(p2.compile_predicate()))
