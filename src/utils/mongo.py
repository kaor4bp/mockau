from motor.motor_asyncio import AsyncIOMotorClient, AsyncIOMotorCollection, AsyncIOMotorCursor
from pymongo.results import DeleteResult, InsertOneResult, UpdateResult

from settings import MockauSettings


class MongoClient:
    def __init__(self, *, collection: str):
        self._client = AsyncIOMotorClient(MockauSettings.mongo.uri)
        self._db = self._client[MockauSettings.mongo.db_name]
        self._collection = self._db[collection]

    def close(self):
        self._client.close()

    @property
    def collection(self) -> AsyncIOMotorCollection:
        return self._collection

    async def ping_server(self):
        await self._client.admin.command('ping')

    async def insert_one(self, document: dict) -> InsertOneResult:
        return await self.collection.insert_one(document)

    def find(self, filters: dict) -> AsyncIOMotorCursor:
        return self.collection.find(filters)

    async def find_one(self, filters: dict) -> dict:
        return await self.collection.find_one(filters)

    async def update_one(self, filters: dict, update: dict, upsert: bool = False) -> UpdateResult:
        return await self.collection.update_one(filter=filters, update=update, upsert=upsert)

    async def update_many(self, filters: dict, update: dict, upsert: bool = False) -> UpdateResult:
        return await self.collection.update_many(filter=filters, update=update, upsert=upsert)

    async def delete_many(self, filters: dict) -> DeleteResult:
        return await self.collection.delete_many(filter=filters)
