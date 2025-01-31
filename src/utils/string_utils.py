import hashlib
import itertools
from uuid import UUID


def split_string(value, splits: int):
    for indexes in itertools.combinations(range(len(value) + 1), splits - 1):
        prev_index = 0
        parts = []
        for index in indexes:
            parts.append(value[prev_index:index])
            prev_index = index
        parts.append(value[prev_index:])
        yield parts


def hash_string_to_uuid(text: str) -> UUID:
    hashsum = hashlib.shake_256(text.encode('utf8')).hexdigest(16)
    return UUID(bytes=bytes.fromhex(hashsum))


def hash_bytes_to_uuid(data: bytes) -> UUID:
    hashsum = hashlib.shake_256(data).hexdigest(16)
    return UUID(bytes=bytes.fromhex(hashsum))
