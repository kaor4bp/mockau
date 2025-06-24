import pytest

from core.predicates.collections.object_predicates import ObjectContainsSubset, ObjectEqualTo, ObjectHasValue
from core.predicates.logical.logical_predicates import AndPredicate, NotPredicate, OrPredicate
from core.predicates.scalars import (
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    StringContains,
    StringPattern,
)
from utils.formatters import get_params_argv

NOT_INTERSECTIONS = {
    '1': [ObjectEqualTo(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek', 'hello': 'world'})],
    '2': [ObjectEqualTo(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 2})],
    '3': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectContainsSubset(value={'lol': 2})],
    'nested dict': [
        ObjectEqualTo(
            value={
                StringContains(value='llo'): {'lol': 'kek'},
            }
        ),
        ObjectEqualTo(
            value={
                StringContains(value='hello'): ObjectEqualTo(value={'lol': StringContains(value='cheburek')}),
            }
        ),
    ],
    'nested dict strict/unstrict': [
        ObjectEqualTo(
            value={
                StringContains(value='llo'): {'lol': 'kek'},
            }
        ),
        ObjectContainsSubset(
            value={
                StringContains(value='hello'): ObjectContainsSubset(
                    value={'lol': StringContains(value='kek'), 'kek': 2}
                ),
            }
        ),
    ],
    'deeply_nested_objects_with_conflicting_values': [
        ObjectContainsSubset(value={'a': {'b': {'c': IntegerEqualTo(value=1)}}}),
        ObjectContainsSubset(value={'a': {'b': {'c': IntegerEqualTo(value=2)}}}),
    ],
    'not_contains_object_and_equal_to_object': [
        NotPredicate(predicate=ObjectContainsSubset(value={'a': 1})),
        ObjectEqualTo(value={'a': 1}),
    ],
}

INTERSECTIONS = {
    '1': [ObjectEqualTo(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek'})],
    '2': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek'})],
    '4': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek', 'hello': 'world'})],
    '5': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectContainsSubset(value={'lol': 'kek'})],
    '6': [ObjectContainsSubset(value={'lol': 'kek', 'hello': 'world'}), ObjectContainsSubset(value={'lol': 'kek'})],
    'nested dict': [
        ObjectEqualTo(
            value={
                StringContains(value='llo'): {'lol': 'kek'},
            }
        ),
        ObjectEqualTo(
            value={
                StringContains(value='hello'): ObjectEqualTo(value={'lol': StringContains(value='kek')}),
            }
        ),
    ],
    '3': [
        ObjectEqualTo(
            value={
                'kek': IntegerGreaterThan(value=4),
            }
        ),
        ObjectEqualTo(
            value={
                'kek': IntegerGreaterThan(value=24),
            }
        ),
    ],
    'concurrent predicate keys #1': [
        ObjectEqualTo(
            value={
                StringContains(value='ello'): IntegerGreaterThan(value=4),
                StringContains(value='ell'): IntegerGreaterThan(value=1),
            }
        ),
        ObjectEqualTo(
            value={
                'hello': IntegerGreaterThan(value=24),
                'hello_world': IntegerLessThan(value=3),
            }
        ),
    ],
    'concurrent predicate keys #2': [
        ObjectEqualTo(
            value={
                StringContains(value='ell'): IntegerGreaterThan(value=1),
                StringContains(value='ello'): IntegerGreaterThan(value=4),
            }
        ),
        ObjectEqualTo(
            value={
                'hello': IntegerGreaterThan(value=24),
                'hello_world': IntegerLessThan(value=3),
            }
        ),
    ],
    'predicate keys can be equal': [
        ObjectEqualTo(
            value={
                StringContains(value='ello'): IntegerGreaterThan(value=4),
                StringContains(value='ello'): IntegerGreaterThan(value=1),
            }
        ),
        ObjectEqualTo(
            value={
                'hello': IntegerGreaterThan(value=24),
                'hello_world': IntegerLessThan(value=3),
            }
        ),
    ],
    'and': [
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'lol': StringContains(value='hello')}),
                ObjectEqualTo(value={'lol': StringContains(value='world')}),
            ]
        ),
        ObjectEqualTo(value={'lol': 'hello world'}),
    ],
    'not': [
        NotPredicate(predicate=ObjectContainsSubset(value={'hello': StringContains(value='world')})),
        ObjectEqualTo(value={'name': StringContains(value='Maria')}),
    ],
    'not_2': [
        ObjectContainsSubset(value={'hello': StringContains(value='world')}),
        NotPredicate(predicate=ObjectEqualTo(value={'name': StringContains(value='Maria')})),
    ],
}

EQUIVALENTS = {
    '1': [ObjectEqualTo(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek'})],
    '2': [
        ObjectEqualTo(value={'lol': StringContains(value='hello')}),
        ObjectEqualTo(value={'lol': StringPattern(pattern='.*hello.*')}),
    ],
    '3': [
        ObjectEqualTo(value={'lol': IntegerEqualTo(value=1)}),
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'lol': NotPredicate(predicate=IntegerGreaterThan(value=1))}),
                ObjectEqualTo(value={'lol': NotPredicate(predicate=IntegerLessThan(value=1))}),
            ]
        ),
    ],
    '4': [
        ObjectEqualTo(value={'lol': IntegerGreaterOrEqualThan(value=1)}),
        OrPredicate(
            predicates=[
                ObjectEqualTo(value={'lol': IntegerGreaterThan(value=1)}),
                ObjectEqualTo(value={'lol': IntegerEqualTo(value=1)}),
            ]
        ),
    ],
    '5': [
        ObjectEqualTo(value={'lol': {'hello': IntegerGreaterOrEqualThan(value=1)}}),
        # ObjectEqualTo(value={'lol': {'hello': OrPredicate(predicates=[IntegerGreaterOrEqualThan(value=1),  IntegerEqualTo(value=1)])}}),
        OrPredicate(
            predicates=[
                ObjectEqualTo(value={'lol': {'hello': IntegerGreaterThan(value=1)}}),
                ObjectEqualTo(value={'lol': {'hello': IntegerEqualTo(value=1)}}),
            ]
        ),
    ],
    '6': [
        ObjectEqualTo(value={'lol': 'kek', 'hello': 'world'}),
        ObjectEqualTo(value={'hello': 'world', 'lol': 'kek'}),
    ],
    '1 < x < 5 EQUIV 1 <= x <= 5 && x != 1 && x != 5': [
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'hello': IntegerGreaterThan(value=1)}),
                ObjectEqualTo(value={'hello': IntegerLessThan(value=5)}),
            ]
        ),
        AndPredicate(
            predicates=[
                ObjectEqualTo(value={'hello': IntegerGreaterOrEqualThan(value=1)}),
                ObjectEqualTo(value={'hello': IntegerLessOrEqualThan(value=5)}),
                ObjectEqualTo(value={'hello': NotPredicate(predicate=IntegerEqualTo(value=1))}),
                ObjectEqualTo(value={'hello': NotPredicate(predicate=IntegerEqualTo(value=5))}),
            ]
        ),
    ],
}

SUPERSETS = {
    '1': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectContainsSubset(value={'lol': 'kek', 'hello': 'world'})],
    '2': [ObjectContainsSubset(value={'lol': 'kek'}), ObjectEqualTo(value={'lol': 'kek'})],
    '3': [ObjectEqualTo(value={'lol': StringContains(value='kek')}), ObjectEqualTo(value={'lol': 'kek'})],
    '10': [
        ObjectContainsSubset(value={'lol': IntegerGreaterThan(value=1)}),
        ObjectContainsSubset(value={'lol': IntegerGreaterThan(value=2)}),
    ],
    '11': [
        ObjectEqualTo(value={'lol': IntegerGreaterThan(value=1)}),
        ObjectEqualTo(value={'lol': IntegerGreaterThan(value=2)}),
    ],
    '12': [
        ObjectEqualTo(value={'lol': {'kek': IntegerGreaterThan(value=1)}}),
        ObjectEqualTo(value={'lol': {'kek': IntegerGreaterThan(value=2)}}),
    ],
    '13': [
        ObjectContainsSubset(value={'lol': {'kek': IntegerGreaterThan(value=1)}}),
        ObjectEqualTo(value={'lol': {'kek': IntegerGreaterThan(value=2)}}),
    ],
    '14': [
        ObjectContainsSubset(value={'lol': IntegerGreaterThan(value=1)}),
        ObjectEqualTo(value={'lol': IntegerGreaterThan(value=2)}),
    ],
    '15': [
        ObjectEqualTo(value={'lol': 'kek', 'hello': StringContains(value='world')}),
        ObjectEqualTo(value={'hello': 'world', 'lol': 'kek'}),
    ],
    '16': [
        ObjectContainsSubset(value={'a': IntegerGreaterThan(value=0)}),
        ObjectContainsSubset(value={'a': IntegerEqualTo(value=1), 'b': IntegerEqualTo(value=2)}),
    ],
    '17': [
        ObjectHasValue(predicate=IntegerGreaterThan(value=0)),
        ObjectContainsSubset(value={'a': IntegerGreaterThan(value=0), 'b': 'hello'}),
    ],
    # '4': [
    #     NestedObjectEqualTo(value={'hello': 'world'}),
    #     ObjectEqualTo(value={'lol': {'hello': 'world'}})
    # ],
    # '5': [
    #     NestedObjectEqualTo(value={'hello': 'world'}),
    #     ObjectEqualTo(value={'hello': 'world'})
    # ],
    # '6': [
    #     NestedObjectContainsSubset(value={'hello': 'world'}),
    #     ObjectEqualTo(value={'hello': 'world'})
    # ],
    # '7': [
    #     NestedObjectContainsSubset(value={'hello': 'world'}),
    #     OrPredicate(predicates=[
    #         ObjectEqualTo(value={'hello': 'world'}),
    #         ObjectEqualTo(value={'lol': {'hello': 'world'}}),
    #     ])
    # ],
    # '8': [
    #     NestedObjectContainsSubset(value={'a3': 'some_val_1'}),
    #     ObjectEqualTo(value={'a2': {'a3': 'some_val_1'}}),
    # ],
    # '9': [
    #     ObjectEqualTo(
    #         value={
    #             'a1': NestedObjectContainsSubset(value={'a3': 'some_val_1'}),
    #             'b1': 'some_val_2'
    #         }
    #     ),
    #     ObjectEqualTo(value={
    #         'a1': {'a2': {'a3': 'some_val_1'}},
    #         'b1': 'some_val_2'
    #     })
    # ]
}


class TestObjectIsNotIntersectedWith:
    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_not_intersected(self, p1, p2):
        assert not p1.is_intersected_with(p2)

    @pytest.mark.parametrize(['p1', 'p2'], **get_params_argv(NOT_INTERSECTIONS))
    def test_not_intersections_are_symmetrical_not_intersected(self, p1, p2):
        assert not p2.is_intersected_with(p1)


class TestObjectIsSubsetOf:
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


class TestObjectIsSupersetOf:
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


class TestObjectIsIntersectedWith:
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
    'simple dict': [ObjectEqualTo(value={'lol': 'kek'}), {'lol': 'kek'}],
    'nested dict': [
        ObjectEqualTo(
            value={
                'hello': {'lol': 'kek'},
            }
        ),
        {'hello': {'lol': 'kek'}},
    ],
    'with scalar predicates': [
        ObjectEqualTo(value={'key1': StringContains(value='ello'), 'key2': IntegerGreaterThan(value=10)}),
        {'key1': 'hello world', 'key2': 15},
    ],
    'with nested predicates': [
        ObjectEqualTo(value={'key1': ObjectEqualTo(value={'nested': 'value'}), 'key2': IntegerGreaterThan(value=10)}),
        {'key1': {'nested': 'value'}, 'key2': 15},
    ],
    'subset matching': [ObjectContainsSubset(value={'key1': 'value1'}), {'key1': 'value1', 'key2': 'value2'}],
    'nested subset matching': [
        ObjectContainsSubset(value={'level1': ObjectContainsSubset(value={'level2': 'value'})}),
        {'level1': {'level2': 'value', 'extra': 'data'}, 'other': 'info'},
    ],
    'and predicate': [
        AndPredicate(
            predicates=[ObjectContainsSubset(value={'key1': 'value1'}), ObjectContainsSubset(value={'key2': 'value2'})]
        ),
        {'key1': 'value1', 'key2': 'value2', 'key3': 'value3'},
    ],
    'or predicate': [
        OrPredicate(predicates=[ObjectEqualTo(value={'key1': 'wrong'}), ObjectEqualTo(value={'key1': 'correct'})]),
        {'key1': 'correct'},
    ],
}

NOT_MATCHED = {
    'simple dict': [ObjectEqualTo(value={'lol': 'kek'}), {'lol': 'wrong'}],
    'nested dict': [
        ObjectEqualTo(
            value={
                'hello': {'lol': 'kek'},
            }
        ),
        {'hello': {'lol': 'wrong'}},
    ],
    'with scalar predicates': [
        ObjectEqualTo(value={'key1': StringContains(value='ello'), 'key2': IntegerGreaterThan(value=10)}),
        {'key1': 'hello world', 'key2': 5},
    ],
    'with nested predicates': [
        ObjectEqualTo(value={'key1': ObjectEqualTo(value={'nested': 'value'}), 'key2': IntegerGreaterThan(value=10)}),
        {'key1': {'nested': 'wrong'}, 'key2': 15},
    ],
    'subset not matching': [ObjectContainsSubset(value={'key1': 'value1'}), {'key2': 'value2', 'key3': 'value3'}],
    'nested subset not matching': [
        ObjectContainsSubset(value={'level1': ObjectContainsSubset(value={'level2': 'value'})}),
        {'level1': {'wrong': 'data'}, 'other': 'info'},
    ],
    'and predicate': [
        AndPredicate(
            predicates=[ObjectContainsSubset(value={'key1': 'value1'}), ObjectContainsSubset(value={'key2': 'value2'})]
        ),
        {'key1': 'value1', 'key2': 'wrong'},
    ],
    'or predicate': [
        OrPredicate(predicates=[ObjectEqualTo(value={'key1': 'wrong1'}), ObjectEqualTo(value={'key1': 'wrong2'})]),
        {'key1': 'also wrong'},
    ],
}


class TestObjectIsMatched:
    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(MATCHED))
    def test_matched_values_are_matched(self, predicate, value):
        assert predicate.is_matched(value)

    @pytest.mark.parametrize(['predicate', 'value'], **get_params_argv(NOT_MATCHED))
    def test_not_matched_values_are_not_matched(self, predicate, value):
        assert not predicate.is_matched(value)
