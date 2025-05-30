def value_to_predicate(value):
    from core.predicates.base_predicate import BasePredicate
    from core.predicates.collections.object_predicates import ObjectEqualTo
    from core.predicates.scalars import BooleanEqualTo, IntegerEqualTo, NumberEqualTo, StringEqualTo

    if isinstance(value, BasePredicate):
        return value

    if isinstance(value, bool):
        return BooleanEqualTo(value=value)
    elif isinstance(value, str):
        return StringEqualTo(value=value)
    elif isinstance(value, int):
        return IntegerEqualTo(value=value)
    elif isinstance(value, float):
        return NumberEqualTo(value=value)
    elif isinstance(value, dict):
        return ObjectEqualTo(value=value)
    # elif isinstance(value, list):
    #     return ArrayStrictEqualTo(value=value)
    else:
        raise ValueError(f'Unsupported value type: {type(value)}')
