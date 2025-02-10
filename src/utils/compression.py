import gzip
import zlib

import brotli


def detect_and_decompress(data: bytes) -> tuple[str | None, bytes]:
    # Check gzip (magic bytes: 0x1F 0x8B)
    if len(data) >= 2 and data[:2] == b'\x1f\x8b':
        try:
            return 'gzip', gzip.decompress(data)
        except OSError:
            pass

    # Check zlib (magic bytes: 0x78 0x01, 0x78 0x9C, 0x78 0xDA)
    if len(data) >= 2 and data[:2] in [b'\x78\x01', b'\x78\x9c', b'\x78\xda']:
        try:
            return 'zlib', zlib.decompress(data)
        except zlib.error:
            pass

    # Check Brotli (no magic numbers)
    try:
        return 'brotli', brotli.decompress(data)
    except brotli.error:
        pass

    return None, data
