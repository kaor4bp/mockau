import pytest

from core.predicates.collections.array_predicates import ArrayContains, ArrayEqualToWithoutOrder, ArrayStrictEqualTo
from core.predicates.collections.object_predicates import ObjectContainsSubset
from core.predicates.logical.logical_predicates import AndPredicate, NotPredicate
from core.predicates.scalars import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    StringContains,
    StringEqualTo,
    StringPattern,
)
from utils.formatters import get_params_argv

NOT_INTERSECTIONS = {
    'equal_to_and_equal_to_with_diff_len': [
        ArrayStrictEqualTo(value=['lol', 'kek']),
        ArrayStrictEqualTo(value=['lol', 'kek', 'hello']),
    ],
    # 'all_of_and_all_of': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=5)),
    #     ArrayItemAllOf(predicate=IntegerLessThan(value=3))
    # ],
    'equal_to_and_equal_to_with_not_intersected_patterns': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\d+$')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    '7': [
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterThan(value=10)]),
                ArrayStrictEqualTo(value=[IntegerLessThan(value=20)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterThan(value=30)]),
                ArrayStrictEqualTo(value=[IntegerLessThan(value=40)]),
            ]
        ),
    ],
    '8': [
        ArrayStrictEqualTo(value=[ObjectContainsSubset(value={'a': 1})]),
        NotPredicate(predicate=ArrayStrictEqualTo(value=[ObjectContainsSubset(value={'a': 1})])),
    ],
    # '9': [
    #     ArrayItemAnyOf(predicate=ObjectContainsSubset(value={'a': 1})),
    #     NotPredicate(predicate=ArrayItemAnyOf(predicate=ObjectContainsSubset(value={'a': 1})))
    # ]
}

INTERSECTIONS = {
    '1': [ArrayStrictEqualTo(value=['lol', 'kek']), ArrayStrictEqualTo(value=['lol', StringContains(value='kek')])],
    # '3': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     ArrayItemAllOf(predicate=IntegerLessThan(value=4))
    # ],
    '7': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\w+$')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    '8': [
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterThan(value=5)]),
                ArrayStrictEqualTo(value=[IntegerLessThan(value=15)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterThan(value=10)]),
                ArrayStrictEqualTo(value=[IntegerLessThan(value=20)]),
            ]
        ),
    ],
}

EQUIVALENTS = {
    '1': [ArrayContains(value=[1, 2]), ArrayContains(value=[2, 1])],
    # '1': [
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='lol')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='kek')),
    #         ]
    #     ),
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='lol')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='kek')),
    #         ]
    #     ),
    # ],
    # '2': [
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='lol')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='kek')),
    #         ]
    #     ),
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='kek')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='lol')),
    #         ]
    #     ),
    # ],
    '1 < x < 5 EQUIV 1 <= x <= 5 && x != 1 && x != 5': [
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterThan(value=1)]),
                ArrayStrictEqualTo(value=[IntegerLessThan(value=5)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayStrictEqualTo(value=[IntegerGreaterOrEqualThan(value=1)]),
                ArrayStrictEqualTo(value=[IntegerLessOrEqualThan(value=5)]),
                ArrayStrictEqualTo(value=[NotPredicate(predicate=IntegerEqualTo(value=1))]),
                ArrayStrictEqualTo(value=[NotPredicate(predicate=IntegerEqualTo(value=5))]),
            ]
        ),
    ],
    # '3': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=0)),
    #     ArrayItemAllOf(predicate=NotPredicate(predicate=IntegerLessOrEqualThan(value=0)))
    # ],
}

SUPERSETS = {
    '1': [ArrayContains(value=['lol', 'kek']), ArrayEqualToWithoutOrder(value=['kek', 'lol'])],
    '5': [ArrayContains(value=['a', 'b']), ArrayContains(value=['a', 'b', 'c'])],
    # '1': [
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='lol')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='kek')),
    #         ]
    #     ),
    #     ArrayEqualToWithoutOrder(value=['kek', 'lol'])
    # ],
    # '5': [
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='a')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='b')),
    #         ]
    #     ),
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='a')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='b')),
    #             ArrayItemAnyOf(predicate=StringEqualTo(value='c')),
    #         ]
    #     ),
    # ],
    '7': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='\w+')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='[a-z]+')]),
    ],
    '9': [
        ArrayStrictEqualTo(value=[StringContains(value='hello')]),
        ArrayStrictEqualTo(value=[StringEqualTo(value='hello world!')]),
    ],
}


class TestArrayIsNotIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_not_intersected(self, p1, p2):
        assert not p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_symmetrical_not_intersected(self, p1, p2):
        assert not p2.is_intersected_with(p1)


class TestArrayIsSubsetOf:
    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_subset_of_another(self, m1, m2):
        assert m1.is_subset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_subset_is_subset_of_superset(self, m1, m2):
        assert m2.is_subset_of(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_superset_is_not_subset_of_subset(self, m1, m2):
        assert not m1.is_subset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_subset_of_equivalents_is_symmetric(self, m1, m2):
        assert m2.is_subset_of(m1)


class TestArrayIsSupersetOf:
    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_superset_is_superset_of_subset(self, m1, m2):
        assert m1.is_superset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_subset_is_not_superset_of_superset(self, m1, m2):
        assert not m2.is_superset_of(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_superset_of_another(self, m1, m2):
        assert m1.is_superset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_superset_of_equivalents_is_symmetric(self, m1, m2):
        assert m2.is_superset_of(m1)


class TestArrayIsIntersectedWith:
    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_intersected(self, m1, m2):
        assert m1.is_intersected_with(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_symmetrical_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_intersected(self, m1, m2):
        assert m1.is_intersected_with(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_symmetrically_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_superset_and_subset_are_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **get_params_argv(SUPERSETS))
    def test_subset_and_superset_are_symmetrically_intersectable(self, m1, m2):
        assert m1.is_intersected_with(m2)


MATCHED = {
    '1': [ArrayStrictEqualTo(value=['hello', 'world']), ['hello', 'world']],
    '2': [ArrayStrictEqualTo(value=[IntegerGreaterOrEqualThan(value=1), 'world']), [2, 'world']],
    '3': [ArrayEqualToWithoutOrder(value=['hello', 'world']), ['world', 'hello']],
    # '4': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 3, 4]
    # ],
    '7': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['123', 'abc'],
    ],
    # '9': [
    #     AndPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringContains(value='error')),
    #             ArrayItemAnyOf(predicate=StringContains(value='warning')),
    #         ]
    #     ),
    #     ['fatal error', 'serious warning']
    # ],
    # '10': [
    #     ArrayItemAllOf(predicate=StringPattern(pattern='^(error|warning|info)$')),
    #     ['error', 'warning', 'info']
    # ]
}

NOT_MATCHED = {
    '1': [ArrayStrictEqualTo(value=['hello', 'world']), ['hello', 'wrong']],
    '2': [ArrayStrictEqualTo(value=[IntegerGreaterOrEqualThan(value=1), 'world']), [0, 'world']],
    '3': [ArrayStrictEqualTo(value=['hello', 'world']), ['world', 'hello']],
    # '4': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 0, 4]
    # ],
    # '7': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 3, 'hello']
    # ],
    '9': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['123', 'ABC'],
    ],
    # '10': [
    #     AndPredicate(predicates=[
    #         ArrayItemAllOf(predicate=IntegerGreaterThan(value=0)),
    #         ArrayItemAnyOf(predicate=StringContains(value='ok'))
    #     ]),
    #     [1, 2, 'status: fail']
    # ],
    # '11': [
    #     OrPredicate(
    #         predicates=[
    #             ArrayItemAnyOf(predicate=StringContains(value='error')),
    #             ArrayItemAnyOf(predicate=StringContains(value='warning')),
    #         ]
    #     ),
    #     ['fatal error', 'serious notice']
    # ],
    # '12': [
    #     ArrayItemAllOf(predicate=StringPattern(pattern='^(error|warning|info)$')),
    #     ['error', 'warning', 'debug']
    # ],
    # '13': [
    #     ArrayItemAllOf(
    #         predicate=OrPredicate(
    #             predicates=[StringEqualTo(value='warning'), StringEqualTo(value='error')]
    #         )
    #     ),
    #     ['error', 'info']
    # ],
    '14': [ArrayEqualToWithoutOrder(value=['required', 'fields']), ['required', 'other']],
}


class TestArrayIsMatched:
    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_matched_values_are_matched(self, predicate, value):
        assert predicate.is_matched(value)

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(NOT_MATCHED))
    def test_not_matched_values_are_not_matched(self, predicate, value):
        assert not predicate.is_matched(value)


# def test_lol():
#     p1 = ArrayContains(value=[1,2])
#     p2 = ArrayContains(value=[1,2,3])
#
#     assert p1.is_superset_of(p2)
