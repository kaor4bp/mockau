from motor.motor_asyncio import AsyncIOMotorClient, AsyncIOMotorCollection, AsyncIOMotorCursor
from pymongo.results import InsertOneResult, UpdateResult


class MongoClient:
    def __init__(self, collection: str):
        self._uri = "mongodb://127.0.0.1:27017"  # host.docker.internal
        self._client = AsyncIOMotorClient(self._uri)
        self._db = self._client["saas_qa_configs"]
        self._collection = self._db[collection]

    @classmethod
    def create_actions_manager(cls) -> 'MongoClient':
        return cls('mockau_new_actions')

    @classmethod
    def create_events_manager(cls) -> 'MongoClient':
        return cls('mockau_events')

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
