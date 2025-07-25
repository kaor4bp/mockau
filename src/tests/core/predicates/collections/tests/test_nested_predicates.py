from core.predicates import (
    AndPredicate,
    AnyPredicate,
    DynamicKeyMatch,
    NestedAllOf,
    NestedAnyOf,
    NestedNoneOf,
    ObjectContainsSubset,
    ObjectEqualTo,
    StringContains,
    StringEqualTo,
)


def test_nested_any_of_string():
    p = NestedAnyOf(predicate=StringEqualTo(value='world'))
    assert p.is_matched({'hello': 'world'})


def test_nested_all_keys_hack():
    p = AndPredicate(
        predicates=[
            NestedAllOf(
                predicate=ObjectContainsSubset(
                    dynamic_matches=[
                        DynamicKeyMatch(
                            key=StringContains(value='world', var='my_var_1'), value=AnyPredicate(var='my_var_1')
                        ),
                    ]
                )
            ),
            NestedAllOf(predicate=StringEqualTo(value='world', var='my_var_1')),
        ]
    )
    assert p.is_matched({'world': 'world'})


def test_1():
    p1 = NestedAnyOf(predicate=ObjectEqualTo(value={'hello': 'world'}))
    p2 = ObjectEqualTo(value={'hello': 'world'})
    assert p1.is_superset_of(p2)


def test_2():
    p1 = NestedNoneOf(predicate=ObjectEqualTo(value={'hello': 'world'}))
    p2 = ObjectEqualTo(value={'hello': 'world'})
    assert not p1.is_intersected_with(p2)


def test_3():
    p1 = NestedNoneOf(predicate=ObjectEqualTo(value={'hello': 'world'}))
    p2 = ObjectEqualTo(value={'hello': 'lol'})
    assert p1.is_intersected_with(p2)
