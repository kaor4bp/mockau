import itertools


def split_string(value, splits: int):
    for indexes in itertools.combinations(range(len(value) + 1), splits - 1):
        prev_index = 0
        parts = []
        for index in indexes:
            parts.append(value[prev_index:index])
            prev_index = index
        parts.append(value[prev_index:])
        yield parts
