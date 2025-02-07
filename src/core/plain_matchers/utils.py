from core.plain_matchers.common_plain_matchers import And, Any


def zip_plain_matchers(plain_matchers):
    if len(plain_matchers) == 0:
        return Any()
    elif len(plain_matchers) == 1:
        return plain_matchers[0]
    else:
        return And(*plain_matchers)
