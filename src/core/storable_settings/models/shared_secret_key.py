import secrets
from typing import Literal

import cryptography
import cryptography.exceptions
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

from core.bases.base_schema import BaseSchema
from core.storable_settings.common import StorableSettingsType
from core.storable_settings.exceptions import SharedSecretKeyInvalidTag
from core.storable_settings.models.base_storable_settings import BaseStorableSettings
from mockau_fastapi import MockauSharedClients


class CipherData(BaseSchema):
    data: bytes
    tag: bytes

    def to_string(self) -> str:
        return f'{self.data.hex()}|{self.tag.hex()}'

    @classmethod
    def from_string(cls, string: str) -> 'CipherData':
        data, tag = string.split('|')
        return cls(data=bytes.fromhex(data), tag=bytes.fromhex(tag))


class SharedSecretKey(BaseStorableSettings):
    type_of: Literal['SHARED_SECRET_KEY'] = 'SHARED_SECRET_KEY'
    secret_key: bytes
    iv: bytes

    @classmethod
    def _test_key(cls, key: bytes, iv: bytes) -> None:
        shared_secret_key = SharedSecretKey(secret_key=key, iv=iv)
        test_string = b'hello world'

        encrypted_string = shared_secret_key.encrypt(test_string)
        decrypted_string = shared_secret_key.decrypt(encrypted_string)

        assert decrypted_string == test_string, 'Decryption failed'

    @classmethod
    async def get_or_create(cls, clients: MockauSharedClients) -> 'SharedSecretKey':
        document = await clients.mongo_settings_client.find_one(
            filters={'type_of': StorableSettingsType.SHARED_SECRET_KEY.value},
        )
        if document:
            return cls.model_validate(document)

        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA256(),
            length=32,
            salt=secrets.token_bytes(256),
            iterations=100000,
        )
        key = kdf.derive(secrets.token_bytes(1024))
        iv = secrets.token_bytes(16)

        cls._test_key(key, iv)

        await clients.mongo_settings_client.update_one(
            filters={'type_of': StorableSettingsType.SHARED_SECRET_KEY.value},
            update={
                '$setOnInsert': {
                    'secret_key': key,
                    'iv': iv,
                    'type_of': 'SHARED_SECRET_KEY',
                }
            },
            upsert=True,
        )
        return cls.model_validate(
            await clients.mongo_settings_client.find_one(
                filters={'type_of': StorableSettingsType.SHARED_SECRET_KEY.value}
            )
        )

    def encrypt(self, data: bytes) -> CipherData:
        cipher = Cipher(algorithms.AES(self.secret_key), modes.GCM(self.iv))
        encryptor = cipher.encryptor()
        ciphertext = encryptor.update(data) + encryptor.finalize()
        return CipherData(
            data=ciphertext,
            tag=encryptor.tag,
        )

    def decrypt(self, cipher_data: CipherData) -> bytes:
        cipher = Cipher(algorithms.AES(self.secret_key), modes.GCM(self.iv, cipher_data.tag))
        decryptor = cipher.decryptor()
        try:
            return decryptor.update(cipher_data.data) + decryptor.finalize()
        except cryptography.exceptions.InvalidTag as exc:
            raise SharedSecretKeyInvalidTag from exc
