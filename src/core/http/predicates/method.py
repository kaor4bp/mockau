from core.http.interaction.common import HttpMethod
from core.predicates import StringInList
from core.predicates.base_predicate import BaseMetaPredicate


class MethodAnyOfPredicate(BaseMetaPredicate):
    one_of: list[HttpMethod]

    def compile_predicate(self):
        return StringInList(values=[item.value for item in self.any_of])


if __name__ == '__main__':
    p1 = MethodAnyOfPredicate(one_of=[HttpMethod.GET, HttpMethod.POST])
    p2 = MethodAnyOfPredicate(one_of=[HttpMethod.GET, HttpMethod.POST, HttpMethod.PUT])

    print(p1.compile_predicate().is_subset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_superset_of(p2.compile_predicate()))
    print(p1.compile_predicate().is_intersected_with(p2.compile_predicate()))
