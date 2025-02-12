import hashlib
from uuid import uuid4

from core.storable_settings.models.shared_secret_key import CipherData
from settings import MockauSettings


def generate_traceparent_token(current_token: str | None = None):
    # version = 00
    # trace-id - unique for every request chain
    # parent-id - unique for every request
    # trace-flags = 01 - force trace saving
    # Example 00-a9c3b99a95cc045e573e163c3ac80a77-d99d251a8caecd06-01

    if current_token is not None:
        _, trace_id, _, _ = current_token.split('-')
    else:
        trace_id = uuid4().hex

    version = '00'
    trace_flags = '01'
    parent_id = hashlib.shake_256(uuid4().bytes).hexdigest(8)

    return f'{version}-{trace_id}-{parent_id}-{trace_flags}'


def generate_encrypted_traceparent_token(current_token: str | None = None) -> str:
    traceparent_token = generate_traceparent_token(current_token)
    return MockauSettings.shared_secret_key.encrypt(traceparent_token.encode('utf-8')).to_string()


def decrypt_traceparent_token(encrypted_token: str) -> str:
    return MockauSettings.shared_secret_key.decrypt(CipherData.from_string(encrypted_token)).decode('utf-8')
