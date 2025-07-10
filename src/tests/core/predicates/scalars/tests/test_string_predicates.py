import pytest

from core.predicates import AndPredicate, AnyPredicate, OrPredicate, StringContains, StringEqualTo, StringPattern
from utils.formatters import get_params_argv

EQUIVALENTS = {
    'equal_to identical to equal_to': [
        StringEqualTo(value='holmes'),
        StringEqualTo(value='holmes'),
    ],
    'contains identical to contains': [
        StringContains(value='holmes'),
        StringContains(value='holmes'),
    ],
    'pattern identical to pattern': [
        StringPattern(pattern='holmes.*'),
        StringPattern(pattern='holmes.*'),
    ],
    'pattern identical to contains': [
        StringPattern(pattern='.*holmes.*'),
        StringContains(value='holmes'),
    ],
    'limited pattern identical to equal_to': [
        StringPattern(pattern='holmes'),
        StringEqualTo(value='holmes'),
    ],
    'equal_to with ignore_case identical to equal_to with ignore_case': [
        StringEqualTo(value='Holmes', ignore_case=True),
        StringEqualTo(value='holmes', ignore_case=True),
    ],
    'contains with ignore_case identical to contains with ignore_case': [
        StringContains(value='holmes', ignore_case=True),
        StringContains(value='holmes', ignore_case=True),
    ],
    'pattern with ignore_case identical to pattern with ignore_case': [
        StringPattern(pattern='holmes.*', ignore_case=True),
        StringPattern(pattern='holmes.*', ignore_case=True),
    ],
    'any pattern identical to empty contains': [
        StringPattern(pattern='.*'),
        StringContains(value=''),
    ],
}

SUPERSETS = {
    'pattern superset of equal_to': [
        StringPattern(pattern='holmes(.*)'),
        StringEqualTo(value='holmes221B'),
    ],
    'contains superset of equal_to': [
        StringContains(value='holmes'),
        StringEqualTo(value='holmes watson'),
    ],
    'equal_to with ignore case superset of equal_to': [
        StringEqualTo(value='Holmes', ignore_case=True),
        StringEqualTo(value='holmes'),
    ],
    'pattern with ignore case superset of pattern': [
        StringPattern(pattern='Holmes.*', ignore_case=True),
        StringPattern(pattern='holmes.*'),
    ],
}

INTERSECTIONS = {
    'pattern intersected with pattern': [
        StringPattern(pattern='holmes watson.*'),
        StringPattern(pattern='.*holmes watson'),
    ],
    'contains intersected with contains': [
        StringContains(value='holmes'),
        StringContains(value='olmes'),
    ],
    'pattern with ignore case intersected with pattern': [
        StringPattern(pattern='Holmes watson.*', ignore_case=True),
        StringPattern(pattern='.*Holmes watson'),
    ],
    'contains with ignore case intersected with contains': [
        StringContains(value='holmes', ignore_case=True),
        StringContains(value='OLMES'),
    ],
}


class TestStringIsSubsetOf:
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


class TestStringIsSupersetOf:
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


class TestStringIsIntersectedWith:
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


class TestStringIsEquivalentTo:
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


class TestStringPredicates:
    # StringEqualTo tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'ignore_case', 'expected'],
        [
            ['holmes', 'holmes', False, True],  # exact match
            ['MORIARTY', 'moriarty', True, True],  # case insensitive match
            ['holmes', 'watson', False, False],  # no match
            ['MORIARTY', 'moriarty', False, False],  # case sensitive mismatch
        ],
        ids=lambda x: repr(x),
    )
    def test_string_equal_to(self, value, test_value, ignore_case, expected):
        predicate = StringEqualTo(value=value, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # StringPattern tests
    @pytest.mark.parametrize(
        ['pattern', 'test_value', 'ignore_case', 'expected'],
        [
            ['holmes.*', 'holmes watson', False, True],  # pattern match
            ['MORIARTY.*', 'moriarty schemes', True, True],  # case insensitive pattern
            ['holmes.*', 'HOLMES watson', False, False],  # case sensitive mismatch
            ['lestrade\\d+', 'lestrade221B', False, True],  # digits pattern
            ['lestrade\\d+', 'lestradeinspector', False, False],  # pattern mismatch
        ],
        ids=lambda x: repr(x),
    )
    def test_string_pattern(self, pattern, test_value, ignore_case, expected):
        predicate = StringPattern(pattern=pattern, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # StringContains tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'ignore_case', 'expected'],
        [
            ['olmes', 'holmes watson', False, True],  # contains substring
            ['MORIARTY', 'holmes moriarty', True, True],  # case insensitive contains
            ['MORIARTY', 'holmes moriarty', False, False],  # case sensitive not contains
            ['watson', 'holmes', False, False],  # doesn't contain
        ],
        ids=lambda x: repr(x),
    )
    def test_string_contains(self, value, test_value, ignore_case, expected):
        predicate = StringContains(value=value, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # NotPredicate tests
    @pytest.mark.parametrize(
        ['predicate', 'test_value', 'expected'],
        [
            [StringEqualTo(value='holmes'), 'holmes', False],  # not equal
            [StringEqualTo(value='holmes'), 'watson', True],  # not equal
            [StringContains(value='olmes'), 'holmes', False],  # not (contains)
            [StringContains(value='clue'), 'holmes', True],  # not (not contains)
        ],
        ids=lambda x: repr(x),
    )
    def test_string_not(self, predicate, test_value, expected):
        not_predicate = ~predicate
        assert not_predicate.is_matched(test_value) == expected

    # AndPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[StringEqualTo(value='holmes'), StringContains(value='olm')], 'holmes', True],  # both true
            [[StringEqualTo(value='holmes'), StringContains(value='clue')], 'holmes', False],  # one false
            [[StringPattern(pattern='h.*s'), StringContains(value='olm')], 'holmes', True],  # pattern + contains
        ],
        ids=lambda x: repr(x),
    )
    def test_string_and(self, predicates, test_value, expected):
        and_predicate = AndPredicate(predicates=predicates)
        assert and_predicate.is_matched(test_value) == expected

    # OrPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[StringEqualTo(value='holmes'), StringContains(value='clue')], 'holmes', True],  # first true
            [[StringEqualTo(value='watson'), StringContains(value='olm')], 'holmes', True],  # second true
            [[StringEqualTo(value='watson'), StringPattern(pattern='clue.*')], 'holmes', False],  # both false
        ],
        ids=lambda x: repr(x),
    )
    def test_string_or(self, predicates, test_value, expected):
        or_predicate = OrPredicate(predicates=predicates)
        assert or_predicate.is_matched(test_value) == expected

    # AnyPredicate tests
    def test_string_any(self):
        any_predicate = AnyPredicate()
        assert any_predicate.is_matched('holmes') is True
