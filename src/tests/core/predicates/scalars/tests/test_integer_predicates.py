import pytest

from core.predicates import (
    AndPredicate,
    AnyPredicate,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNotEqualTo,
    OrPredicate,
    RootPredicate,
)
from utils.formatters import get_params_argv

EQUIVALENTS = {
    'x = 1 EQUIV !(x > 1) && !(x < 1)': [
        IntegerEqualTo(value=1),
        AndPredicate(
            predicates=[
                ~IntegerGreaterThan(value=1),
                ~IntegerLessThan(value=1),
            ]
        ),
    ],
    'x >= 1 EQUIV x > 1 || x == 1': [
        IntegerGreaterOrEqualThan(value=1),
        OrPredicate(predicates=[IntegerGreaterThan(value=1), IntegerEqualTo(value=1)]),
    ],
    '1 < x < 5 || x == 1 || x == 5 EQUIV 1 <= x <= 5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        IntegerGreaterThan(value=1),
                        IntegerLessThan(value=5),
                    ]
                ),
                IntegerEqualTo(value=1),
                IntegerEqualTo(value=5),
            ]
        ),
        AndPredicate(predicates=[IntegerGreaterOrEqualThan(value=1), IntegerLessOrEqualThan(value=5)]),
    ],
    '1 < x < 5 EQUIV 1 <= x <= 5 && x != 1 && x != 5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        IntegerGreaterThan(value=1),
                        IntegerLessThan(value=5),
                    ]
                )
            ]
        ),
        AndPredicate(
            predicates=[
                IntegerGreaterOrEqualThan(value=1),
                IntegerLessOrEqualThan(value=5),
                IntegerNotEqualTo(value=1),
                IntegerNotEqualTo(value=5),
            ]
        ),
    ],
}

SUPERSETS = {
    'x >  5 SUPSET x == 6': [IntegerGreaterThan(value=5), IntegerEqualTo(value=6)],
    'x >  5 SUPSET x >  6': [IntegerGreaterThan(value=5), IntegerGreaterThan(value=6)],
    'x >  5 SUPSET x >= 7': [IntegerGreaterThan(value=5), IntegerGreaterOrEqualThan(value=7)],
    'x >= 5 SUPSET x >  5': [IntegerGreaterOrEqualThan(value=5), IntegerGreaterThan(value=5)],
    'x >= 5 SUPSET x >= 6': [IntegerGreaterOrEqualThan(value=5), IntegerGreaterOrEqualThan(value=6)],
    'x <  5 SUPSET x <  4': [IntegerLessThan(value=5), IntegerLessThan(value=4)],
    'x <  5 SUPSET x <= 3': [IntegerLessThan(value=5), IntegerLessOrEqualThan(value=3)],
    'x <= 5 SUPSET x <  5': [IntegerLessOrEqualThan(value=5), IntegerLessThan(value=5)],
    'x <= 5 SUPSET x <= 4': [IntegerLessOrEqualThan(value=5), IntegerLessOrEqualThan(value=4)],
    '1 <= x < 5 SUPSET 1 < x < 5': [
        AndPredicate(
            predicates=[
                IntegerGreaterOrEqualThan(value=1),
                IntegerLessThan(value=5),
            ]
        ),
        AndPredicate(predicates=[IntegerGreaterThan(value=1), IntegerLessThan(value=5)]),
    ],
    '1 < x < 5 || x == 1 SUPSET 1 < x < 5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        IntegerGreaterThan(value=1),
                        IntegerLessThan(value=5),
                    ]
                ),
                IntegerEqualTo(value=1),
            ]
        ),
        AndPredicate(predicates=[IntegerGreaterThan(value=1), IntegerLessThan(value=5)]),
    ],
    '1 < x < 5 || x == 1 || x == 5 SUPSET 1 < x <= 5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        IntegerGreaterThan(value=1),
                        IntegerLessThan(value=5),
                    ]
                ),
                IntegerEqualTo(value=1),
                IntegerEqualTo(value=5),
            ]
        ),
        AndPredicate(predicates=[IntegerGreaterThan(value=1), IntegerLessOrEqualThan(value=5)]),
    ],
    '1 <= x < 5 SUPSET 1 <= x <= 5 && x != 1 && x != 5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        IntegerGreaterOrEqualThan(value=1),
                        IntegerLessThan(value=5),
                    ]
                )
            ]
        ),
        AndPredicate(
            predicates=[
                IntegerGreaterOrEqualThan(value=1),
                IntegerLessOrEqualThan(value=5),
                IntegerNotEqualTo(value=1),
                IntegerNotEqualTo(value=5),
            ]
        ),
    ],
}

INTERSECTIONS = {
    'x >  5 CAP x <  7': [IntegerGreaterThan(value=5), IntegerLessThan(value=7)],
    'x >  5 CAP !(x > 6)': [IntegerGreaterThan(value=5), ~IntegerGreaterThan(value=6)],
    'x >  5 CAP x <= 6': [IntegerGreaterThan(value=5), IntegerLessOrEqualThan(value=6)],
    'x >= 5 CAP x <  6': [IntegerGreaterOrEqualThan(value=5), IntegerLessThan(value=6)],
    'x >= 5 CAP x <= 5': [IntegerGreaterOrEqualThan(value=5), IntegerLessOrEqualThan(value=5)],
    'x >= 5 CAP x <= 6': [IntegerGreaterOrEqualThan(value=5), IntegerLessOrEqualThan(value=6)],
    'x >= 5 CAP !(x > 6)': [IntegerGreaterOrEqualThan(value=5), ~IntegerGreaterThan(value=6)],
    'x >= 5 CAP 6 < x < 8': [
        IntegerGreaterOrEqualThan(value=5),
        AndPredicate(predicates=[IntegerLessThan(value=8), IntegerGreaterThan(value=6)]),
    ],
    'x >= 5 || x <= 2 CAP x > 5 || x <= 2': [
        OrPredicate(predicates=[IntegerGreaterOrEqualThan(value=5), IntegerLessOrEqualThan(value=2)]),
        OrPredicate(predicates=[IntegerGreaterThan(value=5), IntegerLessOrEqualThan(value=2)]),
    ],
}


class TestIntegerIsSubsetOf:
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


class TestIntegerIsSupersetOf:
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


class TestIntegerIsIntersectedWith:
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


class TestIntegerIsEquivalentTo:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_equivalent(self, p1, p2):
        assert p1.is_equivalent_to(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(EQUIVALENTS))
    def test_equivalents_are_symmetrically_equivalent(self, p1, p2):
        assert p2.is_equivalent_to(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_subset_is_not_equivalent_to_superset(self, p1, p2):
        assert not p2.is_equivalent_to(p1)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(SUPERSETS))
    def test_superset_is_not_equivalent_to_subset(self, p1, p2):
        assert not p1.is_equivalent_to(p2)


class TestIntegerPredicates:
    # IntegerEqualTo tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5, 5, True],  # exact match
            [5, 5.0, False],  # float with .0 should not match
            [5, 6, False],  # not equal
            [0, -0, True],  # zero equality
        ],
    )
    def test_integer_equal_to_valid(self, value, test_value, expected):
        predicate = IntegerEqualTo(value=value)
        assert predicate.is_matched(test_value) == expected

    def test_integer_equal_to_invalid_float(self):
        predicate = IntegerEqualTo(value=5)
        assert not predicate.is_matched(5.1)

    # IntegerGreaterThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5, 6, True],  # greater
            [5, 5, False],  # equal
            [5, 4, False],  # less
        ],
    )
    def test_integer_greater_than(self, value, test_value, expected):
        predicate = IntegerGreaterThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # IntegerGreaterOrEqualThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5, 6, True],  # greater
            [5, 5, True],  # equal
            [5, 4, False],  # less
        ],
    )
    def test_integer_greater_or_equal_than(self, value, test_value, expected):
        predicate = IntegerGreaterOrEqualThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # IntegerLessThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5, 4, True],  # less
            [5, 5, False],  # equal
            [5, 6, False],  # greater
        ],
    )
    def test_integer_less_than(self, value, test_value, expected):
        predicate = IntegerLessThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # IntegerLessOrEqualThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5, 4, True],  # less
            [5, 5, True],  # equal
            [5, 6, False],  # greater
        ],
    )
    def test_integer_less_or_equal_than(self, value, test_value, expected):
        predicate = IntegerLessOrEqualThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # NotPredicate tests
    @pytest.mark.parametrize(
        ['predicate', 'test_value', 'expected'],
        [
            [IntegerEqualTo(value=5), 5, False],  # not equal (false)
            [IntegerEqualTo(value=5), 6, True],  # not equal (true)
            [IntegerGreaterThan(value=5), 6, False],  # not greater (false)
            [IntegerGreaterThan(value=5), 4, True],  # not greater (true)
        ],
    )
    def test_integer_not(self, predicate, test_value, expected):
        not_predicate = ~predicate
        assert not_predicate.is_matched(test_value) == expected

    # AndPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[IntegerEqualTo(value=5), IntegerLessThan(value=10)], 5, True],  # both true
            [[IntegerEqualTo(value=5), IntegerLessThan(value=10)], 11, False],  # one false
            [[IntegerGreaterThan(value=0), IntegerLessThan(value=10)], 5, True],  # range check
            [[IntegerGreaterThan(value=5), IntegerLessThan(value=10)], 10, False],  # boundary check
        ],
    )
    def test_integer_and(self, predicates, test_value, expected):
        and_predicate = AndPredicate(predicates=predicates)
        assert and_predicate.is_matched(test_value) == expected

    # OrPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[IntegerEqualTo(value=5), IntegerEqualTo(value=10)], 5, True],  # first true
            [[IntegerEqualTo(value=5), IntegerEqualTo(value=10)], 10, True],  # second true
            [[IntegerEqualTo(value=5), IntegerEqualTo(value=10)], 7, False],  # both false
        ],
    )
    def test_integer_or(self, predicates, test_value, expected):
        or_predicate = OrPredicate(predicates=predicates)
        assert or_predicate.is_matched(test_value) == expected

    # AnyPredicate tests
    def test_integer_any(self):
        any_predicate = AnyPredicate()
        assert any_predicate.is_matched(123) is True


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
