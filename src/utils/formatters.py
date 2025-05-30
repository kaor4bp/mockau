import math
from typing import Any

MAX_BODY_SIZE_BYTES = 100 * 1024


def format_bytes_size_to_human_readable(size_bytes: int, force_sign: bool = False) -> str:
    """Convert bytes count into human readable format"""

    if size_bytes == 0:
        return "0B"
    if size_bytes < 0:
        sign = '-'
        size_bytes = abs(size_bytes)
    elif force_sign:
        sign = '+'
    else:
        sign = ''

    size_name = ("b", "Kb", "Mb", "Gb", "Tb", "Pb", "Eb", "Zb", "Yb")
    i = int(math.floor(math.log(size_bytes, 1024)))
    p = math.pow(1024, i)
    s = round(size_bytes / p, 2)

    return f'{sign}{s} {size_name[i]}'


def get_params_argv(params: dict[str, Any]):
    return {'argvalues': list(params.values()), 'ids': list(params.keys())}
