from core.predicates import (
    AndPredicate,
    AnyPredicate,
    ArrayEqualTo,
    BooleanEqualTo,
    ObjectEqualTo,
    OrPredicate,
    StringContains,
    StringEqualTo,
)


class TestUserVariables:
    def test_1(self):
        p1 = ArrayEqualTo(
            value=[
                {'1': AnyPredicate(var='hello')},
                {'2': AnyPredicate(var='hello')},
            ]
        )
        p2 = ArrayEqualTo(
            value=[
                {'1': 1},
                {'2': 1},
            ]
        )
        assert p1.is_intersected_with(p2)

    def test_2(self):
        p1 = ArrayEqualTo(
            value=[
                {'lol': StringContains(value='hello')},
                AnyPredicate(var='hello'),
                AnyPredicate(var='hello'),
            ]
        )
        p2 = ArrayEqualTo(
            value=[{'lol': StringContains(value='hello')}, {'1': {'hello': 'world'}}, {'2': {'hello': 'world!!!'}}]
        )
        assert not p1.is_superset_of(p2)

    def test_2_1(self):
        p1 = ArrayEqualTo(
            value=[
                {'lol': StringContains(value='hello')},
                AnyPredicate(var='hello'),
                AnyPredicate(var='hello'),
            ]
        )
        p2 = ArrayEqualTo(value=[{'lol': StringContains(value='hello')}, {'1': 1}, {'2': 2}])
        assert not p1.is_superset_of(p2)

    def test_3(self):
        p1 = AnyPredicate(var='hello')
        p2 = StringEqualTo(value='hello world')
        assert p1.is_superset_of(p2)

    def test_4(self):
        p1 = ArrayEqualTo(
            value=[
                AnyPredicate(var='hello'),
                AnyPredicate(var='hello'),
            ]
        )
        p2 = ArrayEqualTo(
            value=[
                [1, 2, 3],
                [1, 2, 3],
            ]
        )
        assert p1.is_intersected_with(p2)

    def test_5(self):
        p1 = ArrayEqualTo(
            value=[
                AnyPredicate(var='hello'),
                AnyPredicate(var='hello'),
            ]
        )
        p2 = ArrayEqualTo(
            value=[
                {'hello': 'world'},
                {'hello': 'world'},
            ]
        )
        assert p1.is_intersected_with(p2)

    def test_6(self):
        p1 = ArrayEqualTo(
            value=[
                AnyPredicate(var='hello'),
                {'lol': AnyPredicate(var='hello')},
            ]
        )
        p2 = ArrayEqualTo(
            value=[
                {'hello': 'world'},
                {'lol': {'hello': 'world'}},
            ]
        )
        assert p1.is_superset_of(p2)

    def test_7(self):
        p = ArrayEqualTo(value=[BooleanEqualTo(value=True, var='flag'), BooleanEqualTo(value=True, var='flag')])
        assert p.is_matched([True, True])

    def test_8(self):
        p1 = OrPredicate(
            predicates=[
                StringEqualTo(value='hello'),
                StringEqualTo(value='world'),
            ],
            var='hello',
        )
        p2 = StringEqualTo(value='hello', var='hello')
        assert p1.is_intersected_with(p2)

    def test_hack_to_fetch_variables_from_or_with_objects(self):
        p = AndPredicate(
            predicates=[
                OrPredicate(
                    predicates=[
                        ObjectEqualTo(value={'user': 'admin', 'status': 'active'}),
                        ObjectEqualTo(value={'user': 'user1', 'status': 'inactive'}),
                    ],
                ),
                ObjectEqualTo(
                    value={
                        'user': AnyPredicate(var='user'),
                        'status': AnyPredicate(var='status'),
                    }
                ),
            ]
        )

        assert p.is_matched({'user': 'admin', 'status': 'active'})
