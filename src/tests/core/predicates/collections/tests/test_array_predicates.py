"""
Manually written tests for array predicates, modified by Gemini 2.5 Flash (added extra cases and fixed cases naming)
"""

import pytest

from core.predicates import (
    AndPredicate,
    AnyPredicate,
    ArrayContains,
    ArrayEqualTo,
    ArrayNotContains,
    ArrayNotEqualTo,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNotEqualTo,
    NestedArrayContains,
    NestedArrayEqualTo,
    ObjectContainsSubset,
    ObjectEqualTo,
    RootPredicate,
    StringContains,
    StringEqualTo,
    StringPattern,
    VoidPredicate,
)
from utils.formatters import get_params_argv

NOT_INTERSECTIONS = {
    'strict_equal_with_diff_length': [
        ArrayEqualTo(value=[StringEqualTo(value='Alpha'), StringEqualTo(value='Beta')]),
        ArrayEqualTo(value=[StringEqualTo(value='Alpha'), StringEqualTo(value='Beta'), StringEqualTo(value='Gamma')]),
    ],
    'strict_equal_with_not_intersecting_patterns': [
        ArrayEqualTo(value=[StringPattern(pattern='^\\d+$')]),
        ArrayEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    'strict_equal_with_non_overlapping_integer_ranges': [
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
    'object_contains_subset_and_its_negation': [
        ArrayEqualTo(value=[ObjectContainsSubset(value={'caste': 'Alpha'})]),
        ArrayNotEqualTo(value=[ObjectContainsSubset(value={'caste': 'Alpha'})]),
    ],
    'array_contains_and_strict_equal_no_overlap': [
        ArrayContains(value=[StringEqualTo(value='soma'), StringEqualTo(value='feelies')]),
        ArrayEqualTo(
            value=[
                StringEqualTo(value='hypnopaedia'),
                StringEqualTo(value='bokanovsky'),
                StringEqualTo(value='decanting'),
            ]
        ),
    ],
    'strict_equal_with_different_types': [
        ArrayEqualTo(value=['Alpha']),
        ArrayEqualTo(value=[IntegerEqualTo(value=1)]),
    ],
    'array_equal_without_order_different_lengths': [
        ArrayEqualTo(value=['John', 'Lenina'], ignore_order=True),
        ArrayEqualTo(value=['John', 'Lenina', 'Bernard'], ignore_order=True),
    ],
}

INTERSECTIONS = {
    'strict_equal_with_pattern_match': [
        ArrayEqualTo(value=['Alpha', 'Beta']),
        ArrayEqualTo(value=['Alpha', StringContains(value='eta')]),
    ],
    'strict_equal_with_overlapping_patterns': [
        ArrayEqualTo(value=[StringPattern(pattern='^\\w+$')]),
        ArrayEqualTo(value=[StringPattern(pattern='^[a-z]+$')]),
    ],
    'strict_equal_with_overlapping_integer_ranges': [
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
    'array_contains_and_strict_equal_with_common_elements': [
        ArrayContains(value=['soma', 'feelies', 'soma']),
        ArrayEqualTo(value=['soma', 'feelies', 'soma', 'Ford']),
    ],
    # 'nested_array_contains_and_strict_equal_complex': [
    #     NestedArrayContains(value=[NestedObjectEqualTo(value={'society_level': 'Alpha'})]),
    #     ArrayEqualTo(
    #         value=[
    #             ArrayContains(
    #                 value=[
    #                     {'caste_system': [{'epsilon': ArrayContains(value=[{'status': {'society_level': 'Alpha'}}])}]}
    #                 ]
    #             )
    #         ]
    #     ),
    # ],
    'strict_equal_with_partial_string_match': [
        ArrayEqualTo(value=['Bernard Marx', 'Lenina Crowne']),
        ArrayEqualTo(value=[StringContains(value='Bernard'), StringContains(value='Crowne')]),
    ],
    'array_equal_without_order_with_common_elements': [
        ArrayEqualTo(value=['John', 'Bernard', 'Lenina'], ignore_order=True),
        ArrayEqualTo(value=['Lenina', 'Bernard', 'John'], ignore_order=True),
    ],
    'strict_equal_with_shared_regex_pattern': [
        ArrayEqualTo(value=[StringPattern(pattern='^\\d{3}$')]),
        ArrayEqualTo(value=[StringPattern(pattern='^63[0-9]$')]),
    ],
}

EQUIVALENTS = {
    'array_contains_order_irrelevant': [ArrayContains(value=[1, 2]), ArrayContains(value=[2, 1])],
    'integer_range_equivalence_via_not': [
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
    'strict_equal_identical': [
        ArrayEqualTo(value=['decanting', 'hypnopaedia']),
        ArrayEqualTo(value=['decanting', 'hypnopaedia']),
    ],
    'array_equal_without_order_identical': [
        ArrayEqualTo(value=['john', 'lenina'], ignore_order=True),
        ArrayEqualTo(value=['lenina', 'john'], ignore_order=True),
    ],
    'nested_strict_equal_identical': [
        NestedArrayEqualTo(value=[{'caste': 'Gamma'}]),
        NestedArrayEqualTo(value=[{'caste': 'Gamma'}]),
    ],
}

SUPERSETS = {
    'strict_equal_pattern_superset': [
        ArrayEqualTo(value=[StringPattern(pattern='\\w+')]),
        ArrayEqualTo(value=[StringPattern(pattern='[a-z]+')]),
    ],
    'strict_equal_contains_superset': [
        ArrayEqualTo(value=[StringContains(value='world', ignore_case=True)]),
        ArrayEqualTo(value=[StringEqualTo(value='Brave New World!')]),
    ],
    'nested_array_strict_equal_superset_flat': [
        NestedArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'array_contains_superset_of_strict_equal': [
        ArrayContains(value=['Epsilon', 'Gamma']),
        ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_strict_equal_superset_object_value': [
        NestedArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayEqualTo(
            value=[
                ObjectEqualTo(value={'society_ranks': ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
            ]
        ),
    ],
    'nested_array_strict_equal_superset_direct_object': [
        NestedArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'world_castes': ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'nested_array_contains_superset_strict_equal': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_subset_elements': [
        NestedArrayContains(value=['Delta', 'Epsilon']),
        ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_array_contains': [
        NestedArrayContains(value=['Delta', 'Epsilon']),
        ArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
    ],
    'nested_array_contains_superset_of_nested_object_value': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ArrayEqualTo(
            value=[
                ObjectEqualTo(value={'world_castes': ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
            ]
        ),
    ],
    'nested_array_contains_superset_of_direct_object_value': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'caste_system': ArrayEqualTo(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'nested_array_contains_superset_of_array_contains_in_object': [
        NestedArrayContains(value=['Delta', 'Epsilon', 'Gamma']),
        ObjectEqualTo(value={'caste_system': ArrayContains(value=['Delta', 'Epsilon', 'Gamma'])}),
    ],
    'not_strict_equal_superset_of_not_contains': [
        ArrayNotEqualTo(value=['Alpha', 'Beta', 'Gamma']),
        ArrayNotContains(value=['Alpha', 'Beta', 'Gamma']),
    ],
    'nested_array_contains_with_mixed_types': [
        NestedArrayContains(value=[632, 'Mustapha', None]),
        ArrayEqualTo(value=[632, 'Mustapha', None]),
    ],
    'array_equal_without_order_is_superset_of_strict_equal_superset': [
        ArrayEqualTo(value=['A', 'B', 'C'], ignore_order=True),
        ArrayEqualTo(value=['A', 'B', 'C']),
    ],
}


class TestArrayIsNotIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_intersection_with_any(self, p1, p2):
        assert p1.is_intersected_with(AnyPredicate())
        assert p2.is_intersected_with(AnyPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersection_with_void(self, p1, p2):
        assert not p1.is_intersected_with(VoidPredicate())
        assert not p2.is_intersected_with(VoidPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_not_intersected(self, p1, p2):
        assert not p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_symmetrical_not_intersected(self, p1, p2):
        assert not p2.is_intersected_with(p1)


class TestArrayIsSubsetOf:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_intersection_of_superset_with_any(self, p1, p2):
        assert p1.is_intersected_with(AnyPredicate())
        assert p2.is_intersected_with(AnyPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_intersection_of_equivalents_with_any(self, p1, p2):
        assert p1.is_intersected_with(AnyPredicate())
        assert p2.is_intersected_with(AnyPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_not_intersection_of_superset_with_void(self, p1, p2):
        assert not p1.is_intersected_with(VoidPredicate())
        assert not p2.is_intersected_with(VoidPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_not_intersection_of_equivalents_with_void(self, p1, p2):
        assert not p1.is_intersected_with(VoidPredicate())
        assert not p2.is_intersected_with(VoidPredicate())

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
    def test_intersection_with_any(self, p1, p2):
        assert p1.is_intersected_with(AnyPredicate())
        assert p2.is_intersected_with(AnyPredicate())

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(INTERSECTIONS))
    def test_not_intersection_with_void(self, p1, p2):
        assert not p1.is_intersected_with(VoidPredicate())
        assert not p2.is_intersected_with(VoidPredicate())

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
    'strict_equal_simple_match': [ArrayEqualTo(value=['Alpha', 'Beta']), ['Alpha', 'Beta']],
    'strict_equal_integer_and_string_match': [
        ArrayEqualTo(value=[IntegerGreaterOrEqualThan(value=600), 'World']),
        [632, 'World'],
    ],
    'strict_equal_pattern_match': [
        ArrayEqualTo(value=[StringPattern(pattern='^\\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['236', 'gamma'],
    ],
    'array_contains_match_with_mixed_types': [
        ArrayContains(value=[StringEqualTo(value='soma'), IntegerEqualTo(value=96)]),
        ['feelies', 'soma', 96, 'hypnopaedia'],
    ],
    'array_equal_without_order_match': [
        ArrayEqualTo(value=['John', 'Lenina'], ignore_order=True),
        ['Lenina', 'John'],
    ],
    'nested_array_strict_equal_match': [
        NestedArrayEqualTo(value=[{'caste': 'Alpha'}, {'caste': 'Beta'}]),
        [{'caste': 'Alpha'}, {'caste': 'Beta'}],
    ],
    'nested_array_contains_match': [
        NestedArrayContains(value=[ObjectContainsSubset(value={'id': IntegerGreaterThan(value=10)})]),
        [{'id': 11, 'name': 'Unit 11'}, {'id': 12, 'name': 'Unit 12'}],
    ],
}

NOT_MATCHED = {
    'strict_equal_value_mismatch': [ArrayEqualTo(value=['Alpha', 'Beta']), ['Alpha', 'Gamma']],
    'strict_equal_integer_range_mismatch': [
        ArrayEqualTo(value=[IntegerGreaterOrEqualThan(value=632), 'World']),
        [236, 'World'],
    ],
    'strict_equal_order_mismatch': [ArrayEqualTo(value=['Alpha', 'Beta']), ['Beta', 'Alpha']],
    'strict_equal_pattern_case_mismatch': [
        ArrayEqualTo(value=[StringPattern(pattern='^\\d+$'), StringPattern(pattern='^[a-z]+$')]),
        ['236', 'GAMMA'],
    ],
    'array_contains_missing_value': [ArrayContains(value=['John', 'Linda']), ['John', 'Bernard']],
    'array_equal_without_order_length_mismatch': [
        ArrayEqualTo(value=['John', 'Lenina'], ignore_order=True),
        ['John', 'Lenina', 'Bernard'],
    ],
    'nested_array_strict_equal_value_mismatch': [
        NestedArrayEqualTo(value=[{'caste': 'Alpha'}]),
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


class TestEquivalence:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalent_predicates_are_equivalent(self, p1, p2):
        assert p1.is_equivalent_to(p2)

    # @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    # def test_equivalent_predicates_under_not_are_equivalent(self, p1, p2):
    #     p1 = NotPredicate(predicate=p1)
    #     p2 = NotPredicate(predicate=p2)
    #     assert p1.is_equivalent_to(p2)


class TestConsistency:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(dict(**INTERSECTIONS, **EQUIVALENTS, **SUPERSETS)))
    def test_is_consistent(self, p1, p2):
        assert p1.is_consistent()
        assert p2.is_consistent()


class TestSelfEquality:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(dict(**INTERSECTIONS, **EQUIVALENTS, **SUPERSETS)))
    def test_predicate_is_equivalent_to_itself(self, p1, p2):
        assert p1.is_equal_to(p1)
        assert p2.is_equal_to(p2)


class TestSerialization:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(dict(**INTERSECTIONS, **EQUIVALENTS, **SUPERSETS)))
    def test_json_dump(self, p1, p2):
        p1.model_dump_json()
        p2.model_dump_json()

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(dict(**INTERSECTIONS, **EQUIVALENTS, **SUPERSETS)))
    def test_json_load(self, p1, p2):
        restored_p1 = RootPredicate.model_validate_json(p1.model_dump_json(by_alias=True))
        assert restored_p1.root.is_equal_to(p1)
        restored_p2 = RootPredicate.model_validate_json(p2.model_dump_json(by_alias=True))
        assert restored_p2.root.is_equal_to(p2)
