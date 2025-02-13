import pytest

from core.plain_matchers.object_plain_matchers import ObjectPlainMatcher
from core.plain_matchers.string_plain_matchers import StringAny, StringEqualTo, StringPattern

EQUIVALENTS = {
    'argvalues': [
        [
            ObjectPlainMatcher(obj={'hello': StringEqualTo(value='world')}),
            ObjectPlainMatcher(
                obj={
                    StringEqualTo(value='hello'): StringEqualTo(value='world'),
                }
            ),
        ]
    ],
    'ids': [
        'object and identical object with StringEqualTo key',
    ],
}

SUPERSETS = {
    'argvalues': [
        [
            ObjectPlainMatcher(obj={'hello': StringEqualTo(value='hello')}),
            ObjectPlainMatcher(
                obj={
                    'hello': StringEqualTo(value='hello'),
                    'world': StringAny(),
                }
            ),
        ],
        [
            ObjectPlainMatcher(obj={StringEqualTo(value='hello'): StringEqualTo(value='hello')}),
            ObjectPlainMatcher(
                obj={
                    'hello': StringEqualTo(value='hello'),
                    StringPattern(pattern='world.*'): StringAny(),
                }
            ),
        ],
        [
            ObjectPlainMatcher(
                obj={
                    StringPattern(pattern='hello.*'): StringEqualTo(value='hello'),
                    StringPattern(pattern='hello.*'): StringEqualTo(value='hello'),
                }
            ),
            ObjectPlainMatcher(
                obj={
                    'hello1': StringEqualTo(value='hello'),
                    'hello2': StringEqualTo(value='hello'),
                }
            ),
        ],
    ],
    'ids': [
        'object superset of object',
        'object with StringEqualTo key superset of object',
        'object with StringPattern superset of object with two matched keys',
    ],
}


class TestObjectIsSubsetOf:
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


class TestObjectIsSupersetOf:
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


class TestObjectIsEquivalentTo:
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
