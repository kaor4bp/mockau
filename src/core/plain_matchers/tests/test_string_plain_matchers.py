import pytest

from core.plain_matchers.string_plain_matchers import StringContains, StringEqualTo, StringPattern

EQUIVALENTS = {
    'argvalues': [
        [StringEqualTo(value='hello'), StringEqualTo(value='hello')],
        [StringContains(value='hello'), StringContains(value='hello')],
        [StringPattern(pattern='hello.*'), StringPattern(pattern='hello.*')],
        [StringPattern(pattern='.*hello.*'), StringContains(value='hello')],
        [StringPattern(pattern='hello'), StringEqualTo(value='hello')],
        [StringEqualTo(value='hello', ignore_case=True), StringEqualTo(value='hello', ignore_case=True)],
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
        [StringPattern(pattern='hello.*'), StringEqualTo(value='hello123')],
        [StringContains(value='hello'), StringEqualTo(value='hello world')],
        [StringPattern(pattern='hello.[1-4]'), StringPattern(pattern='hello.[1-3]')],
        [StringEqualTo(value='Hello', ignore_case=True), StringEqualTo(value='hello')],
        [StringPattern(pattern='Hello.*', ignore_case=True), StringPattern(pattern='hello.*')],
    ],
    'ids': [
        'pattern superset of equal_to',
        'contains superset of equal_to',
        'pattern superset of pattern',
        'equal_to with ignore case superset of equal_to',
        'pattern with ignore case superset of pattern',
    ],
}


class TestStringIsSubsetOf:
    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_one_equivalent_is_subset_of_another(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_subset_of(x2)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_subset_is_subset_of_superset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_subset_of(x1)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_superset_is_not_subset_of_subset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert not x1.is_subset_of(x2)

    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_subset_of_equivalents_is_symmetric(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_subset_of(x1)


class TestStringIsSupersetOf:
    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_superset_is_superset_of_subset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_superset_of(x2)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_subset_is_not_superset_of_superset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert not x2.is_superset_of(x1)

    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_one_equivalent_is_superset_of_another(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_superset_of(x2)

    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_superset_of_equivalents_is_symmetric(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_superset_of(x1)


class TestStringIsIntersectedWith:
    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_equivalents_are_intersectable(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_intersected_with(x2)

    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_equivalents_are_symmetrically_intersectable(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_intersected_with(x1)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_superset_and_subset_are_intersectable(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_intersected_with(x1)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_subset_and_superset_are_symmetrically_intersectable(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_intersected_with(x2)


class TestStringIsEquivalentTo:
    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_equivalents_are_equivalent(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x1.is_equivalent_to(x2)

    @pytest.mark.parametrize('matchers_pair', **EQUIVALENTS)
    def test_equivalents_are_symmetrically_equivalent(self, matchers_pair):
        x1, x2 = matchers_pair
        assert x2.is_equivalent_to(x1)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_subset_is_not_equivalent_to_superset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert not x2.is_equivalent_to(x1)

    @pytest.mark.parametrize('matchers_pair', **SUPERSETS)
    def test_superset_is_not_equivalent_to_subset(self, matchers_pair):
        x1, x2 = matchers_pair
        assert not x1.is_equivalent_to(x2)
