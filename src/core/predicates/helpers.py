from core.predicates.base_predicate import MOCKAU_TYPE


def py_value_to_predicate(value):
    from core.predicates import (
        ArrayStrictEqualTo,
        BooleanEqualTo,
        IntegerEqualTo,
        IsNull,
        NumberEqualTo,
        ObjectEqualTo,
        StringEqualTo,
    )
    from core.predicates.base_predicate import BasePredicate

    if isinstance(value, BasePredicate):
        return value

    if isinstance(value, bool):
        return BooleanEqualTo(value=value)
    elif isinstance(value, str):
        return StringEqualTo(value=value)
    elif isinstance(value, float):
        return NumberEqualTo(value=value)
    elif isinstance(value, int):
        return IntegerEqualTo(value=value)
    elif isinstance(value, list):
        return ArrayStrictEqualTo(value=value)
    elif isinstance(value, dict):
        if value.get('__x_mockau_type') == MOCKAU_TYPE or value.get('x_mockau_type') == MOCKAU_TYPE:
            return value
        else:
            return ObjectEqualTo(value=value)
    elif value is None:
        return IsNull()
    else:
        raise ValueError(f'Unsupported value type: {type(value)}')
