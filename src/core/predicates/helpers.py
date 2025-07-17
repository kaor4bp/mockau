from copy import deepcopy


def deserialize_json_predicate_format(value):
    if (
        isinstance(value, dict)
        and len(value.keys()) == 1
        and isinstance(list(value.keys())[0], str)
        and list(value.keys())[0].startswith('$-mockau-')
    ):
        new_data = list(value.values())[0]
        new_data['type_of'] = list(value.keys())[0]
        value = new_data

    if isinstance(value, list):
        value = deepcopy(value)
        value = [deserialize_json_predicate_format(item) for item in value]

    if isinstance(value, dict):
        value = deepcopy(value)
        for k, v in value.items():
            value[k] = deserialize_json_predicate_format(v)

    return value


def py_value_to_predicate(value):
    from core.predicates import (
        ArrayEqualTo,
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

    value = deepcopy(value)

    if isinstance(value, bool):
        return BooleanEqualTo(value=value)
    elif isinstance(value, str):
        return StringEqualTo(value=value)
    elif isinstance(value, float):
        return NumberEqualTo(value=value)
    elif isinstance(value, int):
        return IntegerEqualTo(value=value)
    elif isinstance(value, list):
        return ArrayEqualTo(value=value)
    elif isinstance(value, dict):
        if value.get('type_of', '').startswith('$-mockau-'):
            return value
        else:
            return ObjectEqualTo(value=value)
    elif value is None:
        return IsNull()
    else:
        raise ValueError(f'Unsupported value type: {type(value)}')
