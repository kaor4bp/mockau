import pytest

from core.predicates import (
    AndPredicate,
    AnyPredicate,
    NumberEqualTo,
    NumberGreaterOrEqualThan,
    NumberGreaterThan,
    NumberLessOrEqualThan,
    NumberLessThan,
    OrPredicate,
)
from core.predicates.scalars.number_predicates import NumberNotEqualTo
from utils.formatters import get_params_argv

EQUIVALENTS = {
    # Базовые эквивалентности
    'x = 1.0 EQUIV !(x > 1.0) && !(x < 1.0)': [
        NumberEqualTo(value=1.0),
        AndPredicate(
            predicates=[
                ~NumberGreaterThan(value=1.0),
                ~NumberLessThan(value=1.0),
            ]
        ),
    ],
    'x = 1.5 EQUIV !(x > 1.5) && !(x < 1.5)': [
        NumberEqualTo(value=1.5),
        AndPredicate(
            predicates=[
                ~NumberGreaterThan(value=1.5),
                ~NumberLessThan(value=1.5),
            ]
        ),
    ],
    # Граничные значения и точность
    'x = 0.0 EQUIV !(x > 0.0) && !(x < 0.0)': [
        NumberEqualTo(value=0.0),
        AndPredicate(
            predicates=[
                ~NumberGreaterThan(value=0.0),
                ~NumberLessThan(value=0.0),
            ]
        ),
    ],
    'x = 0.0001 EQUIV !(x > 0.0001) && !(x < 0.0001)': [
        NumberEqualTo(value=0.0001),
        AndPredicate(
            predicates=[
                ~NumberGreaterThan(value=0.0001),
                ~NumberLessThan(value=0.0001),
            ]
        ),
    ],
    # Комбинированные условия
    'x >= 1.0 EQUIV x > 1.0 || x == 1.0': [
        NumberGreaterOrEqualThan(value=1.0),
        OrPredicate(predicates=[NumberGreaterThan(value=1.0), NumberEqualTo(value=1.0)]),
    ],
    'x >= 1.5 EQUIV x > 1.5 || x == 1.5': [
        NumberGreaterOrEqualThan(value=1.5),
        OrPredicate(predicates=[NumberGreaterThan(value=1.5), NumberEqualTo(value=1.5)]),
    ],
    # Диапазоны с дробными значениями
    '1.2 < x < 4.8 || x == 1.2 || x == 4.8 EQUIV 1.2 <= x <= 4.8': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        NumberGreaterThan(value=1.2),
                        NumberLessThan(value=4.8),
                    ]
                ),
                NumberEqualTo(value=1.2),
                NumberEqualTo(value=4.8),
            ]
        ),
        AndPredicate(predicates=[NumberGreaterOrEqualThan(value=1.2), NumberLessOrEqualThan(value=4.8)]),
    ],
    '0.5 < x < 5.5 EQUIV 0.5 <= x <= 5.5 && x != 0.5 && x != 5.5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        NumberGreaterThan(value=0.5),
                        NumberLessThan(value=5.5),
                    ]
                )
            ]
        ),
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=0.5),
                NumberLessOrEqualThan(value=5.5),
                NumberNotEqualTo(value=0.5),
                NumberNotEqualTo(value=5.5),
            ]
        ),
    ],
    # Добавляем тест с отрицательными числами
    '-2.5 < x < -1.5 EQUIV -2.5 <= x <= -1.5 && x != -2.5 && x != -1.5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        NumberGreaterThan(value=-2.5),
                        NumberLessThan(value=-1.5),
                    ]
                )
            ]
        ),
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=-2.5),
                NumberLessOrEqualThan(value=-1.5),
                NumberNotEqualTo(value=-2.5),
                NumberNotEqualTo(value=-1.5),
            ]
        ),
    ],
}

SUPERSETS = {
    # Базовые суперсеты
    'x > 5.0 SUPSET x == 6.0': [NumberGreaterThan(value=5.0), NumberEqualTo(value=6.0)],
    'x > 5.0 SUPSET x == 5.1': [NumberGreaterThan(value=5.0), NumberEqualTo(value=5.1)],
    'x > 5.0 SUPSET x > 5.1': [NumberGreaterThan(value=5.0), NumberGreaterThan(value=5.1)],
    # Граничные случаи
    'x > 5.0 SUPSET x > 5.000001': [NumberGreaterThan(value=5.0), NumberGreaterThan(value=5.000001)],
    'x > 0.0 SUPSET x > 0.000001': [NumberGreaterThan(value=0.0), NumberGreaterThan(value=0.000001)],
    # Отрицательные значения
    'x > -5.0 SUPSET x == -4.0': [NumberGreaterThan(value=-5.0), NumberEqualTo(value=-4.0)],
    'x > -5.0 SUPSET x > -4.9': [NumberGreaterThan(value=-5.0), NumberGreaterThan(value=-4.9)],
    # Комплексные условия
    '1.1 <= x < 5.9 SUPSET 1.2 < x < 5.8': [
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=1.1),
                NumberLessThan(value=5.9),
            ]
        ),
        AndPredicate(predicates=[NumberGreaterThan(value=1.2), NumberLessThan(value=5.8)]),
    ],
    # Дополнительные вариации диапазонов
    '0.5 < x < 5.5 || x == 0.5 SUPSET 0.5 < x < 5.5': [
        OrPredicate(
            predicates=[
                AndPredicate(
                    predicates=[
                        NumberGreaterThan(value=0.5),
                        NumberLessThan(value=5.5),
                    ]
                ),
                NumberEqualTo(value=0.5),
            ]
        ),
        AndPredicate(predicates=[NumberGreaterThan(value=0.5), NumberLessThan(value=5.5)]),
    ],
    # Тест с очень маленькими числами
    '0.0001 <= x < 0.0002 SUPSET 0.00011 < x < 0.00019': [
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=0.0001),
                NumberLessThan(value=0.0002),
            ]
        ),
        AndPredicate(predicates=[NumberGreaterThan(value=0.00011), NumberLessThan(value=0.00019)]),
    ],
}

INTERSECTIONS = {
    # Базовые пересечения
    'x > 5.0 CAP x < 7.0': [NumberGreaterThan(value=5.0), NumberLessThan(value=7.0)],
    'x > 5.5 CAP x < 6.5': [NumberGreaterThan(value=5.5), NumberLessThan(value=6.5)],
    # Граничные случаи
    'x > 5.0 CAP x < 5.000001': [NumberGreaterThan(value=5.0), NumberLessThan(value=5.000001)],
    'x > 0.0 CAP x < 0.000001': [NumberGreaterThan(value=0.0), NumberLessThan(value=0.000001)],
    # Отрицательные значения
    'x > -5.0 CAP x < -3.0': [NumberGreaterThan(value=-5.0), NumberLessThan(value=-3.0)],
    'x >= -4.5 CAP x <= -3.5': [NumberGreaterOrEqualThan(value=-4.5), NumberLessOrEqualThan(value=-3.5)],
    # Комплексные условия
    'x >= 5.0 CAP x < 6.0': [NumberGreaterOrEqualThan(value=5.0), NumberLessThan(value=6.0)],
    'x >= 5.5 CAP x <= 5.5': [NumberGreaterOrEqualThan(value=5.5), NumberLessOrEqualThan(value=5.5)],
    # Дополнительные вариации
    'x >= 5.0 CAP 6.0 < x < 8.0': [
        NumberGreaterOrEqualThan(value=5.0),
        AndPredicate(predicates=[NumberLessThan(value=8.0), NumberGreaterThan(value=6.0)]),
    ],
    # Тест с очень маленькими диапазонами
    '0.0001 <= x <= 0.0002 CAP 0.00015 <= x <= 0.00025': [
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=0.0001),
                NumberLessOrEqualThan(value=0.0002),
            ]
        ),
        AndPredicate(
            predicates=[
                NumberGreaterOrEqualThan(value=0.00015),
                NumberLessOrEqualThan(value=0.00025),
            ]
        ),
    ],
    # Специальный тест для проверки точности
    'x >= 1.23456789 CAP x <= 1.23456790': [
        NumberGreaterOrEqualThan(value=1.23456789),
        NumberLessOrEqualThan(value=1.23456790),
    ],
}


class TestNumberIsSubsetOf:
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


class TestNumberIsSupersetOf:
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


class TestNumberIsIntersectedWith:
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


class TestNumberIsEquivalentTo:
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


class TestNumberPredicates:
    # NumberEqualTo tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5.0, 5.0, True],  # exact float match
            [5.0, 5, False],  # int to float equality
            [5.5, 5.5, True],  # float with decimal
            [5.0, 5.1, False],  # not equal
            [0.0, -0.0, True],  # zero equality
            [1.23, 1.23, True],  # precise float
            [1.23, 1.230, True],  # float precision
        ],
    )
    def test_number_equal_to(self, value, test_value, expected):
        predicate = NumberEqualTo(value=value)
        assert predicate.is_matched(test_value) == expected

    # NumberGreaterThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5.0, 6.0, True],  # greater float
            [5.0, 5.0001, True],  # slightly greater
            [5.0, 5.0, False],  # equal
            [5.0, 4.9999, False],  # slightly less
            [5.5, 5.6, True],  # decimal greater
            [5.5, 5.4, False],  # decimal less
        ],
    )
    def test_number_greater_than(self, value, test_value, expected):
        predicate = NumberGreaterThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # NumberGreaterOrEqualThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5.0, 6.0, True],  # greater
            [5.0, 5.0, True],  # equal
            [5.0, 4.9999, False],  # less
            [5.5, 5.5, True],  # decimal equal
            [5.5, 5.6, True],  # decimal greater
        ],
    )
    def test_number_greater_or_equal_than(self, value, test_value, expected):
        predicate = NumberGreaterOrEqualThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # NumberLessThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5.0, 4.0, True],  # less
            [5.0, 4.9999, True],  # slightly less
            [5.0, 5.0, False],  # equal
            [5.0, 5.0001, False],  # slightly greater
            [5.5, 5.4, True],  # decimal less
        ],
    )
    def test_number_less_than(self, value, test_value, expected):
        predicate = NumberLessThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # NumberLessOrEqualThan tests
    @pytest.mark.parametrize(
        ['value', 'test_value', 'expected'],
        [
            [5.0, 4.0, True],  # less
            [5.0, 5.0, True],  # equal
            [5.0, 5.0001, False],  # greater
            [5.5, 5.5, True],  # decimal equal
            [5.5, 5.4, True],  # decimal less
        ],
    )
    def test_number_less_or_equal_than(self, value, test_value, expected):
        predicate = NumberLessOrEqualThan(value=value)
        assert predicate.is_matched(test_value) == expected

    # NotPredicate tests
    @pytest.mark.parametrize(
        ['predicate', 'test_value', 'expected'],
        [
            [NumberEqualTo(value=5.0), 5.0, False],
            [NumberEqualTo(value=5.5), 5.5, False],
            [NumberEqualTo(value=5.0), 5.1, True],
            [NumberGreaterThan(value=5.0), 6.0, False],
            [NumberGreaterThan(value=5.5), 5.6, False],
            [NumberGreaterThan(value=5.0), 4.0, True],
        ],
    )
    def test_number_not(self, predicate, test_value, expected):
        not_predicate = ~predicate
        assert not_predicate.is_matched(test_value) == expected

    # AndPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[NumberEqualTo(value=5.0), NumberLessThan(value=10.0)], 5.0, True],
            [[NumberEqualTo(value=5.5), NumberLessThan(value=10.0)], 5.5, True],
            [[NumberEqualTo(value=5.0), NumberLessThan(value=10.0)], 11.0, False],
            [[NumberGreaterThan(value=0.5), NumberLessThan(value=10.5)], 5.0, True],
            [[NumberGreaterThan(value=1.1), NumberLessThan(value=9.9)], 5.5, True],
        ],
    )
    def test_number_and(self, predicates, test_value, expected):
        and_predicate = AndPredicate(predicates=predicates)
        assert and_predicate.is_matched(test_value) == expected

    # OrPredicate tests
    @pytest.mark.parametrize(
        ['predicates', 'test_value', 'expected'],
        [
            [[NumberEqualTo(value=5.0), NumberEqualTo(value=10.0)], 5.0, True],
            [[NumberEqualTo(value=5.5), NumberEqualTo(value=10.5)], 5.5, True],
            [[NumberEqualTo(value=5.0), NumberEqualTo(value=10.0)], 10.0, True],
            [[NumberEqualTo(value=5.0), NumberEqualTo(value=10.0)], 7.5, False],
            [[NumberGreaterThan(value=5.0), NumberLessThan(value=3.0)], 6.0, True],
            [[NumberGreaterThan(value=5.5), NumberLessThan(value=3.5)], 2.0, True],
        ],
    )
    def test_number_or(self, predicates, test_value, expected):
        or_predicate = OrPredicate(predicates=predicates)
        assert or_predicate.is_matched(test_value) == expected

    # AnyPredicate tests
    @pytest.mark.parametrize(
        ['test_value'],
        [
            [0.0],
            [5.0],
            [5.5],
            [-10.0],
            [123.456],
        ],
    )
    def test_number_any(self, test_value):
        any_predicate = AnyPredicate()
        assert any_predicate.is_matched(test_value) is True
