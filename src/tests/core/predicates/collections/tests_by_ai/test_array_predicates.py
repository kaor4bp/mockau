import pytest

from core.predicates import (
    AndPredicate,
    ArrayContains,
    ArrayEqualTo,
    ArrayNotContains,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNotEqualTo,
    ObjectContainsSubset,
    OrPredicate,
    StringContains,
    StringEqualTo,
    StringPattern,
)
from utils.formatters import get_params_argv

# Predicates that should have no common values that satisfy them.
NOT_INTERSECTIONS = {
    'strict_equal_with_different_lengths': [
        ArrayEqualTo(value=['lol', 'kek']),
        ArrayEqualTo(value=['lol', 'kek', 'hello']),
    ],
    # 'all_items_must_be_in_disjoint_integer_ranges': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=5)),
    #     ArrayItemAllOf(predicate=IntegerLessThan(value=3))
    # ],
    'strict_equal_with_disjoint_string_patterns': [
        ArrayEqualTo(value=[StringPattern(pattern=r'^\d+$')]),
        ArrayEqualTo(value=[StringPattern(pattern=r'^[a-z]+$')]),
    ],
    'and_predicate_with_disjoint_integer_ranges': [
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterThan(value=10)]),
                ArrayEqualTo(value=[IntegerLessThan(value=20)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterThan(value=30)]),
                ArrayEqualTo(value=[IntegerLessThan(value=40)]),
            ]
        ),
    ],
    'contains_object_and_not_contains_object': [
        ArrayContains(value=[{'a': 1}]),
        ArrayNotContains(value=[{'a': 1}]),
    ],
    'strict_equal_to_empty_vs_non_empty': [ArrayEqualTo(value=[]), ArrayEqualTo(value=[1])],
    # 'all_items_greater_than_10_vs_contains_value_less_than_10': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=10)),
    #     ArrayContains(value=[5])
    # ],
    'deeply_nested_objects_with_conflicting_values': [
        ArrayEqualTo(value=[ObjectContainsSubset(value={'a': {'b': {'c': IntegerEqualTo(value=1)}}})]),
        ArrayEqualTo(value=[ObjectContainsSubset(value={'a': {'b': {'c': IntegerEqualTo(value=2)}}})]),
    ],
}

# Predicates that should have at least one common value that satisfies them.
INTERSECTIONS = {
    'strict_equal_with_subset_predicate': [
        ArrayEqualTo(value=['lol', 'kek']),
        ArrayEqualTo(value=['lol', StringContains(value='ke')]),
    ],
    # 'all_items_in_overlapping_integer_ranges': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     ArrayItemAllOf(predicate=IntegerLessThan(value=4))
    # ],
    'strict_equal_with_subset_string_pattern': [
        ArrayEqualTo(value=[StringPattern(pattern=r'^\w+$')]),
        ArrayEqualTo(value=[StringPattern(pattern=r'^[a-z]+$')]),
    ],
    'and_predicate_with_overlapping_integer_ranges': [
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterThan(value=5)]),
                ArrayEqualTo(value=[IntegerLessThan(value=15)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterThan(value=10)]),
                ArrayEqualTo(value=[IntegerLessThan(value=20)]),
            ]
        ),
    ],
    'contains_partially_overlapping_elements': [ArrayContains(value=['a', 'b']), ArrayContains(value=['b', 'c'])],
    # 'all_items_greater_than_5_vs_contains_value_greater_than_5': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=5)),
    #     ArrayContains(value=[10])
    # ],
    'equal_without_order_vs_strict_equal_with_permutation': [
        ArrayEqualTo(value=['a', 'b'], ignore_order=True),
        ArrayEqualTo(value=['b', 'a']),
    ],
    # 'complex_and_intersects_with_simple_or': [
    #     ArrayItemAllOf(predicate=AndPredicate(predicates=[IntegerGreaterThan(value=10), IntegerLessThan(value=20)])),
    #     ArrayItemAllOf(predicate=OrPredicate(predicates=[IntegerEqualTo(value=15), IntegerEqualTo(value=25)]))
    # ]
}

# Pairs of predicates where the set of values matched by each should be identical.
EQUIVALENTS = {
    'contains_is_order_agnostic': [ArrayContains(value=['lol', 'kek']), ArrayContains(value=['kek', 'lol'])],
    'equivalent_integer_range_definitions': [
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterThan(value=1)]),
                ArrayEqualTo(value=[IntegerLessThan(value=5)]),
            ]
        ),
        AndPredicate(
            predicates=[
                ArrayEqualTo(value=[IntegerGreaterOrEqualThan(value=1)]),
                ArrayEqualTo(value=[IntegerLessOrEqualThan(value=5)]),
                ArrayEqualTo(value=[IntegerNotEqualTo(value=1)]),
                ArrayEqualTo(value=[IntegerNotEqualTo(value=5)]),
            ]
        ),
    ],
    # 'equivalent_predicates_using_negation': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=0)),
    #     ArrayItemAllOf(predicate=NotPredicate(predicate=IntegerLessOrEqualThan(value=0)))
    # ],
    'equal_without_order_is_order_agnostic': [
        ArrayEqualTo(value=['a', 'b', 'c'], ignore_order=True),
        ArrayEqualTo(value=['c', 'b', 'a'], ignore_order=True),
    ],
    'strict_equal_with_equivalent_nested_predicates': [
        ArrayEqualTo(value=[IntegerGreaterThan(value=5)]),
        ArrayEqualTo(value=[~IntegerLessOrEqualThan(value=5)]),
    ],
    # De Morgan's law: Not(A or B) is equivalent to (Not A) and (Not B)
    'de_morgans_law_on_nested_predicates': [
        ArrayEqualTo(value=[~OrPredicate(predicates=[IntegerEqualTo(value=1), IntegerEqualTo(value=2)])]),
        ArrayEqualTo(
            value=[
                AndPredicate(
                    predicates=[
                        IntegerNotEqualTo(value=1),
                        IntegerNotEqualTo(value=2),
                    ]
                )
            ]
        ),
    ],
}

# Pairs of predicates where p1 matches a broader set of values than p2 (p1 is a superset of p2).
SUPERSETS = {
    'contains_is_superset_of_equal_without_order': [
        ArrayContains(value=['a', 'b']),
        ArrayEqualTo(value=['a', 'b'], ignore_order=True),
    ],
    'contains_fewer_items_is_superset': [ArrayContains(value=[1, 2]), ArrayContains(value=[1, 2, 3])],
    'strict_equal_with_broader_pattern_is_superset': [
        ArrayEqualTo(value=[StringPattern(pattern='\w+')]),
        ArrayEqualTo(value=[StringPattern(pattern='[a-z]+')]),
    ],
    'string_contains_is_superset_of_string_equal': [
        ArrayEqualTo(value=[StringContains(value='hello')]),
        ArrayEqualTo(value=[StringEqualTo(value='hello world!')]),
    ],
    # 'all_items_with_broader_range_is_superset': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=5)),
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=10))
    # ],
    # 'or_predicate_is_superset_of_its_component': [
    #     ArrayItemAllOf(predicate=OrPredicate(predicates=[IntegerEqualTo(value=1), IntegerEqualTo(value=2)])),
    #     ArrayItemAllOf(predicate=IntegerEqualTo(value=1))
    # ],
}

# Test cases where the predicate should successfully match the value.
MATCHED = {
    'strict_equal_with_exact_match': [ArrayEqualTo(value=['hello', 'world']), ['hello', 'world']],
    'strict_equal_with_nested_predicate_match': [
        ArrayEqualTo(value=[IntegerGreaterOrEqualThan(value=1), 'world']),
        [2, 'world'],
    ],
    'equal_without_order_with_permuted_match': [
        ArrayEqualTo(value=['hello', 'world'], ignore_order=True),
        ['world', 'hello'],
    ],
    # 'all_items_match_predicate': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 3, 4]
    # ],
    'strict_equal_with_multiple_string_patterns': [
        ArrayEqualTo(value=[StringPattern(pattern=r'^\d+$'), StringPattern(pattern=r'^[a-z]+$')]),
        ['123', 'abc'],
    ],
    'contains_with_nested_string_contains': [
        ArrayContains(value=[StringContains(value='error'), StringContains(value='warning')]),
        ['msg: fatal error', 'msg: serious warning', 'other info'],
    ],
    # 'all_items_match_or_pattern': [
    #     ArrayItemAllOf(predicate=StringPattern(pattern=r'^(error|warning|info)$')),
    #     ['error', 'warning', 'info']
    # ],
    'contains_with_nested_object_subset': [
        ArrayContains(value=[ObjectContainsSubset(value={'status': 'ok', 'code': 200})]),
        [{'status': 'ok', 'code': 200, 'data': []}, {'other_obj': True}],
    ],
    'match_on_empty_array': [ArrayEqualTo(value=[]), []],
    'not_predicate_match': [ArrayNotContains(value=[10]), [1, 2, 3]],
    'match_on_deeply_nested_structure': [
        ArrayContains(
            value=[
                ObjectContainsSubset(
                    value={
                        'id': StringPattern(pattern='\d+'),
                        'data': ArrayContains(
                            value=[ObjectContainsSubset(value={'type': 'A', 'value': IntegerGreaterThan(value=10)})]
                        ),
                    }
                )
            ]
        ),
        [{'id': '123', 'data': [{'type': 'A', 'value': 11}, {'type': 'B', 'value': 5}]}],
    ],
}

# Test cases where the predicate should NOT match the value.
NOT_MATCHED = {
    'strict_equal_with_one_wrong_element': [ArrayEqualTo(value=['hello', 'world']), ['hello', 'wrong']],
    'strict_equal_with_failed_nested_predicate': [
        ArrayEqualTo(value=[IntegerGreaterOrEqualThan(value=1), 'world']),
        [0, 'world'],
    ],
    'strict_equal_fails_on_wrong_order': [ArrayEqualTo(value=['hello', 'world']), ['world', 'hello']],
    # 'all_items_fails_if_one_item_is_invalid': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 0, 4]
    # ],
    # 'all_items_fails_on_wrong_type': [
    #     ArrayItemAllOf(predicate=IntegerGreaterThan(value=1)),
    #     [2, 3, 'hello']
    # ],
    'strict_equal_fails_on_string_pattern_mismatch': [
        ArrayEqualTo(value=[StringPattern(pattern=r'^\d+$'), StringPattern(pattern=r'^[a-z]+$')]),
        ['123', 'ABC'],
    ],
    # 'and_predicate_fails_if_one_clause_fails': [
    #     AndPredicate(predicates=[
    #         ArrayItemAllOf(predicate=IntegerGreaterThan(value=0)),
    #         ArrayContains(value=[StringContains(value='ok')])
    #     ]),
    #     [1, 2, 'status: fail']
    # ],
    'contains_fails_if_one_required_item_is_missing': [
        ArrayContains(value=[StringContains(value='error'), StringContains(value='warning')]),
        ['fatal error', 'serious notice'],
    ],
    # 'all_items_fails_on_or_pattern_mismatch': [
    #     ArrayItemAllOf(predicate=StringPattern(pattern=r'^(error|warning|info)$')),
    #     ['error', 'warning', 'debug']
    # ],
    # 'all_items_fails_on_logical_or_mismatch': [
    #     ArrayItemAllOf(
    #         predicate=OrPredicate(
    #             predicates=[StringEqualTo(value='warning'), StringEqualTo(value='error')]
    #         )
    #     ),
    #     ['error', 'info']
    # ],
    'equal_without_order_fails_on_length_mismatch': [
        ArrayEqualTo(value=['required', 'fields'], ignore_order=True),
        ['required', 'fields', 'extra'],
    ],
    'equal_without_order_fails_if_element_is_wrong': [
        ArrayEqualTo(value=['a', 'b'], ignore_order=True),
        ['a', 'c'],
    ],
    'not_predicate_no_match': [ArrayNotContains(value=[10]), [1, 10, 3]],
    'fail_on_deeply_nested_structure_mismatch': [
        ArrayContains(
            value=[
                ObjectContainsSubset(
                    value={
                        'data': ArrayContains(
                            value=[ObjectContainsSubset(value={'type': 'A', 'value': IntegerGreaterThan(value=10)})]
                        )
                    }
                )
            ]
        ),
        [{'id': '123', 'data': [{'type': 'A', 'value': 9}]}],
    ],
}


class TestArrayRelationships:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_not_intersected(self, p1, p2):
        assert not p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_symmetrical(self, p1, p2):
        assert not p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_symmetrical(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_and_subset_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_and_superset_are_symmetrical(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['superset', 'subset'], **get_params_argv(SUPERSETS))
    def test_subset_is_subset_of_superset(self, superset, subset):
        assert subset.is_subset_of(superset)

    @pytest.mark.parametrize(['superset', 'subset'], **get_params_argv(SUPERSETS))
    def test_superset_is_not_subset_of_subset(self, superset, subset):
        assert not superset.is_subset_of(subset)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_subsets_of_each_other(self, p1, p2):
        assert p1.is_subset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_subsets_symmetrically(self, p1, p2):
        assert p2.is_subset_of(p1)

    @pytest.mark.parametrize(['superset', 'subset'], **get_params_argv(SUPERSETS))
    def test_superset_is_superset_of_subset(self, superset, subset):
        assert superset.is_superset_of(subset)

    @pytest.mark.parametrize(['superset', 'subset'], **get_params_argv(SUPERSETS))
    def test_subset_is_not_superset_of_superset(self, superset, subset):
        assert not subset.is_superset_of(superset)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_supersets_of_each_other(self, p1, p2):
        assert p1.is_superset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_supersets_symmetrically(self, p1, p2):
        assert p2.is_superset_of(p1)


class TestArrayMatching:
    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_matched_values_are_matched(self, predicate, value):
        assert predicate.is_matched(value)

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(NOT_MATCHED))
    def test_not_matched_values_are_not_matched(self, predicate, value):
        assert not predicate.is_matched(value)
