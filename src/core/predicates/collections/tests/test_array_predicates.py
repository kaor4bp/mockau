"""
Manually written tests for array predicates, modified by Gemini 2.5 Flash (added extra cases and fixed cases naming)
"""

import pytest

from core.predicates.collections.array_predicates import ArrayContains, ArrayEqualToWithoutOrder, ArrayStrictEqualTo
from core.predicates.collections.nested_predicates import (
    NestedArrayContains,
    NestedArrayStrictEqualTo,
    NestedObjectEqualTo,
)
from core.predicates.collections.object_predicates import ObjectContainsSubset, ObjectEqualTo
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
    'strict_equal_with_diff_length': [
        ArrayStrictEqualTo(value=['Alpha', 'Beta']),
        ArrayStrictEqualTo(value=['Alpha', 'Beta', 'Gamma']),
    ],
    'strict_equal_with_not_intersecting_patterns': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\\d+$')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    'strict_equal_with_non_overlapping_integer_ranges': [
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
    'object_contains_subset_and_its_negation': [
        ArrayStrictEqualTo(value=[ObjectContainsSubset(value={'caste': 'Alpha'})]),
        NotPredicate(predicate=ArrayStrictEqualTo(value=[ObjectContainsSubset(value={'caste': 'Alpha'})])),
    ],
    'array_contains_and_strict_equal_no_overlap': [
        ArrayContains(value=['soma', 'feelies']),
        ArrayStrictEqualTo(value=['hypnopaedia', 'bokanovsky', 'decanting']),
    ],
    'strict_equal_with_different_types': [
        ArrayStrictEqualTo(value=['Alpha']),
        ArrayStrictEqualTo(value=[IntegerEqualTo(value=1)]),
    ],
    'array_equal_without_order_different_lengths': [
        ArrayEqualToWithoutOrder(value=['John', 'Lenina']),
        ArrayEqualToWithoutOrder(value=['John', 'Lenina', 'Bernard']),
    ],
}

INTERSECTIONS = {
    'strict_equal_with_pattern_match': [
        ArrayStrictEqualTo(value=['Alpha', 'Beta']),
        ArrayStrictEqualTo(value=['Alpha', StringContains(value='eta')]),
    ],
    'strict_equal_with_overlapping_patterns': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\\w+$')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    'strict_equal_with_overlapping_integer_ranges': [
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
    'array_contains_and_strict_equal_with_common_elements': [
        ArrayContains(value=['soma', 'feelies', 'soma']),
        ArrayStrictEqualTo(value=['soma', 'feelies', 'soma', 'Ford']),
    ],
    'nested_array_contains_and_strict_equal_complex': [
        NestedArrayContains(value=[NestedObjectEqualTo(value={'society_level': 'Alpha'})]),
        ArrayStrictEqualTo(
            value=[
                ArrayContains(
                    value=[
                        {'caste_system': [{'epsilon': ArrayContains(value=[{'status': {'society_level': 'Alpha'}}])}]}
                    ]
                )
            ]
        ),
    ],
    'strict_equal_with_partial_string_match': [
        ArrayStrictEqualTo(value=['Bernard Marx', 'Lenina Crowne']),
        ArrayStrictEqualTo(value=[StringContains(value='Bernard'), StringContains(value='Crowne')]),
    ],
    'array_equal_without_order_with_common_elements': [
        ArrayEqualToWithoutOrder(value=['John', 'Bernard', 'Lenina']),
        ArrayEqualToWithoutOrder(value=['Lenina', 'Bernard', 'John']),
    ],
    'strict_equal_with_shared_regex_pattern': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\\d{3}$')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='^63[0-9]$')]),
    ],
}

EQUIVALENTS = {
    'array_contains_order_irrelevant': [ArrayContains(value=[1, 2]), ArrayContains(value=[2, 1])],
    'integer_range_equivalence_via_not': [
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
    'strict_equal_identical': [
        ArrayStrictEqualTo(value=['decanting', 'hypnopaedia']),
        ArrayStrictEqualTo(value=['decanting', 'hypnopaedia']),
    ],
    'array_equal_without_order_identical': [
        ArrayEqualToWithoutOrder(value=['john', 'lenina']),
        ArrayEqualToWithoutOrder(value=['lenina', 'john']),
    ],
    'nested_strict_equal_identical': [
        NestedArrayStrictEqualTo(value=[{'caste': 'Gamma'}]),
        NestedArrayStrictEqualTo(value=[{'caste': 'Gamma'}]),
    ],
}

SUPERSETS = {
    'strict_equal_pattern_superset': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='\\w+')]),
        ArrayStrictEqualTo(value=[StringPattern(pattern='[a-z]+')]),
    ],
    'strict_equal_contains_superset': [
        ArrayStrictEqualTo(value=[StringContains(value='world', ignore_case=True)]),
        ArrayStrictEqualTo(value=[StringEqualTo(value='Brave New World!')]),
    ],
    'nested_array_strict_equal_superset_flat': [
        NestedArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'array_contains_superset_of_strict_equal': [
        ArrayContains(value=['Epsilon', 'Gamma']),
        ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_strict_equal_superset_object_value': [
        NestedArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayStrictEqualTo(
            value=[
                ObjectEqualTo(value={'society_ranks': ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
            ]
        ),
    ],
    'nested_array_strict_equal_superset_direct_object': [
        NestedArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'world_castes': ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'nested_array_contains_superset_strict_equal': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_subset_elements': [
        NestedArrayContains(value=['Delta', 'Epsilon']),
        ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_array_contains': [
        NestedArrayContains(value=['Delta', 'Epsilon']),
        ArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_nested_object_value': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayStrictEqualTo(
            value=[
                ObjectEqualTo(value={'world_castes': ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
            ]
        ),
    ],
    'nested_array_contains_superset_of_direct_object_value': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'caste_system': ArrayStrictEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'nested_array_contains_superset_of_array_contains_in_object': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'caste_system': ArrayContains(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'not_strict_equal_superset_of_not_contains': [
        NotPredicate(predicate=ArrayStrictEqualTo(value=['Alpha', 'Beta', 'Gamma'])),
        NotPredicate(predicate=ArrayContains(value=['Alpha', 'Beta', 'Gamma'])),
    ],
    'nested_array_contains_with_mixed_types': [
        NestedArrayContains(value=[632, 'Mustapha', None]),
        ArrayStrictEqualTo(value=[632, 'Mustapha', None]),
    ],
    'array_equal_without_order_is_superset_of_strict_equal_superset': [
        ArrayEqualToWithoutOrder(value=['A', 'B', 'C']),
        ArrayStrictEqualTo(value=['A', 'B', 'C']),
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
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_subset_of_another(self, p1, p2):
        assert p1.is_subset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_is_subset_of_superset(self, p1, p2):
        assert p2.is_subset_of(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_is_not_subset_of_subset(self, p1, p2):
        assert not p1.is_subset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_subset_of_equivalents_is_symmetric(self, p1, p2):
        assert p2.is_subset_of(p1)


class TestArrayIsSupersetOf:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_is_consistent(self, p1, p2):
        assert p1.is_consistent()
        assert p2.is_consistent()

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_is_superset_of_subset(self, p1, p2):
        assert p1.is_superset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_is_not_superset_of_superset(self, p1, p2):
        assert not p2.is_superset_of(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_one_equivalent_is_superset_of_another(self, p1, p2):
        assert p1.is_superset_of(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_superset_of_equivalents_is_symmetric(self, p1, p2):
        assert p2.is_superset_of(p1)


class TestArrayIsIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_is_consistent(self, p1, p2):
        assert p1.is_consistent()
        assert p2.is_consistent()

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_intersections_are_symmetrical_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_intersected(self, p1, p2):
        assert p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_symmetrically_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_and_subset_are_intersected(self, p1, p2):
        assert p2.is_intersected_with(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_and_superset_are_symmetrically_intersectable(self, p1, p2):
        assert p1.is_intersected_with(p2)


MATCHED = {
    'strict_equal_simple_match': [ArrayStrictEqualTo(value=['Alpha', 'Beta']), ['Alpha', 'Beta']],
    'strict_equal_integer_and_string_match': [
        ArrayStrictEqualTo(value=[IntegerGreaterOrEqualThan(value=600), 'World']),
        [632, 'World'],
    ],
    'strict_equal_pattern_match': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['236', 'gamma'],
    ],
    'array_contains_match_with_mixed_types': [
        ArrayContains(value=[StringEqualTo(value='soma'), IntegerEqualTo(value=96)]),
        ['feelies', 'soma', 96, 'hypnopaedia'],
    ],
    'array_equal_without_order_match': [ArrayEqualToWithoutOrder(value=['John', 'Lenina']), ['Lenina', 'John']],
    'nested_array_strict_equal_match': [
        NestedArrayStrictEqualTo(value=[{'caste': 'Alpha'}, {'caste': 'Beta'}]),
        [{'caste': 'Alpha'}, {'caste': 'Beta'}],
    ],
    'nested_array_contains_match': [
        NestedArrayContains(value=[ObjectContainsSubset(value={'id': IntegerGreaterThan(value=10)})]),
        [{'id': 11, 'name': 'Unit 11'}, {'id': 12, 'name': 'Unit 12'}],
    ],
}

NOT_MATCHED = {
    'strict_equal_value_mismatch': [ArrayStrictEqualTo(value=['Alpha', 'Beta']), ['Alpha', 'Gamma']],
    'strict_equal_integer_range_mismatch': [
        ArrayStrictEqualTo(value=[IntegerGreaterOrEqualThan(value=632), 'World']),
        [236, 'World'],
    ],
    'strict_equal_order_mismatch': [ArrayStrictEqualTo(value=['Alpha', 'Beta']), ['Beta', 'Alpha']],
    'strict_equal_pattern_case_mismatch': [
        ArrayStrictEqualTo(value=[StringPattern(pattern='^\\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['236', 'GAMMA'],
    ],
    'array_contains_missing_value': [ArrayContains(value=['John', 'Linda']), ['John', 'Bernard']],
    'array_equal_without_order_length_mismatch': [
        ArrayEqualToWithoutOrder(value=['John', 'Lenina']),
        ['John', 'Lenina', 'Bernard'],
    ],
    'nested_array_strict_equal_value_mismatch': [
        NestedArrayStrictEqualTo(value=[{'caste': 'Alpha'}]),
        [{'caste': 'Beta'}],
    ],
    'nested_array_contains_no_match': [
        NestedArrayContains(value=[{'id': IntegerGreaterThan(value=1000)}]),
        [{'id': 10, 'name': 'Unit 10'}],
    ],
}


class TestArrayIsMatched:
    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_matched_values_are_matched(self, predicate, value):
        assert predicate.is_matched(value)

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(NOT_MATCHED))
    def test_not_matched_values_are_not_matched(self, predicate, value):
        assert not predicate.is_matched(value)
