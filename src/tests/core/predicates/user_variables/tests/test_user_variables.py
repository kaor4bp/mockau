from core.predicates import (
    AndPredicate,
    AnyPredicate,
    ArrayEqualTo,
    AvailableTemplate,
    BooleanEqualTo,
    ObjectEqualTo,
    OrPredicate,
    ResultContext,
    StringConcatEqualTo,
    StringContains,
    StringEqualTo,
    StringTemplate,
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
        result_ctx = ResultContext()
        assert p1.is_intersected_with(p2, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('hello') == 1

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
        result_ctx = ResultContext()
        assert p1.is_intersected_with(p2, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('hello') == [1, 2, 3]

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
        result_ctx = ResultContext()
        assert p1.is_intersected_with(p2, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('hello') == {'hello': 'world'}

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
        result_ctx = ResultContext()
        assert p1.is_superset_of(p2, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('hello') == {'hello': 'world'}

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

        result_ctx = ResultContext()
        assert p1.is_intersected_with(p2, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('hello') == 'hello'

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

        result_ctx = ResultContext()
        assert p.is_matched({'user': 'admin', 'status': 'active'}, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('user') == 'admin'
        assert result_ctx.get_user_var_value('status') == 'active'

    def test_hack_of_lookbehind(self):
        p = StringConcatEqualTo(
            values=[
                StringEqualTo(value='adr_'),
                StringTemplate(
                    template=AvailableTemplate.UUID_V4,
                    var='lol',
                ),
            ],
        )

        result_ctx = ResultContext()
        test_uuid = 'adr_9272b6b0f2184d8198ddda684a4a03b8'
        assert p.is_matched(test_uuid, result_ctx=result_ctx)
        assert result_ctx.get_user_var_value('lol') == '9272b6b0f2184d8198ddda684a4a03b8'
