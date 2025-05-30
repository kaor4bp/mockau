import pytest

from core.predicates.logical.logical_predicates import AndPredicate, AnyPredicate, NotPredicate, OrPredicate
from core.predicates.scalars.string_predicates import StringContains, StringEqualTo, StringPattern

EQUIVALENTS = {
    'argvalues': [
        [StringEqualTo(value='hello'), StringEqualTo(value='hello')],
        [StringContains(value='hello'), StringContains(value='hello')],
        [StringPattern(pattern='hello.*'), StringPattern(pattern='hello.*')],
        [StringPattern(pattern='.*hello.*'), StringContains(value='hello')],
        [StringPattern(pattern='hello'), StringEqualTo(value='hello')],
        [StringEqualTo(value='Hello', ignore_case=True), StringEqualTo(value='hello', ignore_case=True)],
        [StringContains(value='hello', ignore_case=True), StringContains(value='hello', ignore_case=True)],
        [StringPattern(pattern='hello.*', ignore_case=True), StringPattern(pattern='hello.*', ignore_case=True)],
        [StringPattern(pattern='.*'), StringContains(value='')],
    ],
    'ids': [
        'equal_to identical to equal_to',
        'contains identical to contains',
        'pattern identical to pattern',
        'pattern identical to contains',
        'limited pattern identical to equal_to',
        'equal_to with ignore_case identical to equal_to with ignore_case',
        'contains with ignore_case identical to contains with ignore_case',
        'pattern with ignore_case identical to pattern with ignore_case',
        'any pattern identical to empty contains',
    ],
}

SUPERSETS = {
    'argvalues': [
        [StringPattern(pattern='hello(.*)'), StringEqualTo(value='hello123')],
        [StringContains(value='hello'), StringEqualTo(value='hello world')],
        [StringEqualTo(value='Hello', ignore_case=True), StringEqualTo(value='hello')],
        [StringPattern(pattern='Hello.*', ignore_case=True), StringPattern(pattern='hello.*')],
    ],
    'ids': [
        'pattern superset of equal_to',
        'contains superset of equal_to',
        'equal_to with ignore case superset of equal_to',
        'pattern with ignore case superset of pattern',
    ],
}

INTERSECTIONS = {
    'argvalues': [
        [StringPattern(pattern='hello world.*'), StringPattern(pattern='.*hello world')],
        [StringContains(value='hello'), StringContains(value='ello')],
        [StringPattern(pattern='Hello world.*', ignore_case=True), StringPattern(pattern='.*Hello world')],
        [StringContains(value='hello', ignore_case=True), StringContains(value='ElLo')],
    ],
    'ids': [
        'pattern intersected with pattern',
        'contains intersected with contains',
        'pattern with ignore case intersected with pattern',
        'contains with ignore case intersected with contains',
    ],
}


class TestStringIsSubsetOf:
    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_one_equivalent_is_subset_of_another(self, m1, m2):
        assert m1.is_subset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_subset_is_subset_of_superset(self, m1, m2):
        assert m2.is_subset_of(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_superset_is_not_subset_of_subset(self, m1, m2):
        assert not m1.is_subset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_subset_of_equivalents_is_symmetric(self, m1, m2):
        assert m2.is_subset_of(m1)


class TestStringIsSupersetOf:
    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_superset_is_superset_of_subset(self, m1, m2):
        assert m1.is_superset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_subset_is_not_superset_of_superset(self, m1, m2):
        assert not m2.is_superset_of(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_one_equivalent_is_superset_of_another(self, m1, m2):
        assert m1.is_superset_of(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_superset_of_equivalents_is_symmetric(self, m1, m2):
        assert m2.is_superset_of(m1)


class TestStringIsIntersectedWith:
    @pytest.mark.parametrize(['m1', 'm2'], **INTERSECTIONS)
    def test_intersections_are_intersected(self, m1, m2):
        assert m1.is_intersected_with(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **INTERSECTIONS)
    def test_intersections_are_symmetrical_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_equivalents_are_intersected(self, m1, m2):
        assert m1.is_intersected_with(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_equivalents_are_symmetrically_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_superset_and_subset_are_intersected(self, m1, m2):
        assert m2.is_intersected_with(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_subset_and_superset_are_symmetrically_intersectable(self, m1, m2):
        assert m1.is_intersected_with(m2)


class TestStringIsEquivalentTo:
    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_equivalents_are_equivalent(self, m1, m2):
        assert m1.is_equivalent_to(m2)

    @pytest.mark.parametrize(['m1', 'm2'], **EQUIVALENTS)
    def test_equivalents_are_symmetrically_equivalent(self, m1, m2):
        assert m2.is_equivalent_to(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_subset_is_not_equivalent_to_superset(self, m1, m2):
        assert not m2.is_equivalent_to(m1)

    @pytest.mark.parametrize(['m1', 'm2'], **SUPERSETS)
    def test_superset_is_not_equivalent_to_subset(self, m1, m2):
        assert not m1.is_equivalent_to(m2)


class TestStringPredicates:
    # StringEqualTo tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'ignore_case', 'expected'],
        [
            ['hello', 'hello', False, True],  # exact match
            ['HELLO', 'hello', True, True],  # case insensitive match
            ['hello', 'world', False, False],  # no match
            ['HELLO', 'hello', False, False],  # case sensitive mismatch
        ],
    )
    def test_string_equal_to(self, value, test_value, ignore_case, expected):
        predicate = StringEqualTo(value=value, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # StringPattern tests
    @pytest.mark.parametrize(
        ['pattern', 'test_value', 'ignore_case', 'expected'],
        [
            ['hello.*', 'hello world', False, True],  # pattern match
            ['HELLO.*', 'hello world', True, True],  # case insensitive pattern
            ['hello.*', 'HELLO world', False, False],  # case sensitive mismatch
            ['hello\\d+', 'hello123', False, True],  # digits pattern
            ['hello\\d+', 'helloworld', False, False],  # pattern mismatch
        ],
    )
    def test_string_pattern(self, pattern, test_value, ignore_case, expected):
        predicate = StringPattern(pattern=pattern, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # StringContains tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'ignore_case', 'expected'],
        [
            ['llo', 'hello world', False, True],  # contains substring
            ['LLO', 'hello world', True, True],  # case insensitive contains
            ['LLO', 'hello world', False, False],  # case sensitive not contains
            ['world', 'hello', False, False],  # doesn't contain
        ],
    )
    def test_string_contains(self, value, test_value, ignore_case, expected):
        predicate = StringContains(value=value, ignore_case=ignore_case)
        assert predicate.is_matched(test_value) == expected

    # NotPredicate tests
    @pytest.mark.parametrize(
        ['predicate', 'test_value', 'expected'],
        [
            [StringEqualTo(value='hello'), 'hello', False],  # not equal
            [StringEqualTo(value='hello'), 'world', True],  # not equal
            [StringContains(value='llo'), 'hello', False],  # not (contains)
            [StringContains(value='xyz'), 'hello', True],  # not (not contains)
        ],
    )
    def test_string_not(self, predicate, test_value, expected):
        not_predicate = NotPredicate(predicate=predicate)
        assert not_predicate.is_matched(test_value) == expected

    # AndPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[StringEqualTo(value='hello'), StringContains(value='ell')], 'hello', True],  # both true
            [[StringEqualTo(value='hello'), StringContains(value='xyz')], 'hello', False],  # one false
            [[StringPattern(pattern='h.*o'), StringContains(value='ell')], 'hello', True],  # pattern + contains
        ],
    )
    def test_string_and(self, predicates, test_value, expected):
        and_predicate = AndPredicate(predicates=predicates)
        assert and_predicate.is_matched(test_value) == expected

    # OrPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[StringEqualTo(value='hello'), StringContains(value='xyz')], 'hello', True],  # first true
            [[StringEqualTo(value='world'), StringContains(value='ell')], 'hello', True],  # second true
            [[StringEqualTo(value='world'), StringPattern(pattern='xyz.*')], 'hello', False],  # both false
        ],
    )
    def test_string_or(self, predicates, test_value, expected):
        or_predicate = OrPredicate(predicates=predicates)
        assert or_predicate.is_matched(test_value) == expected

    # AnyPredicate tests
    def test_string_any(self):
        any_predicate = AnyPredicate()
        assert any_predicate.is_matched('hello') is True
