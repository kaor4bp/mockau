import elasticsearch
import httpx
from fastapi import FastAPI
from starlette.datastructures import State

from settings import MockauSettings
from utils.mongo import MongoClient


class MockauState(State):
    settings: MockauSettings
    mongo_events_client: MongoClient
    mongo_actions_client: MongoClient
    mongo_settings_client: MongoClient
    elasticsearch_client: elasticsearch.AsyncElasticsearch

    httpx_clients: dict[str, tuple[httpx.AsyncClient, 'HttpClientSettings']]


class MockauFastAPI(FastAPI):
    state: MockauState

    async def init_state(self):
        from models.storable_settings import HttpClientSettings

        self.state.settings = MockauSettings
        self.state.mongo_events_client = MongoClient(collection='mockau_events')
        self.state.mongo_actions_client = MongoClient(collection='mockau_actions')
        self.state.mongo_settings_client = MongoClient(collection='mockau_settings')
        self.state.elasticsearch_client = elasticsearch.AsyncElasticsearch(
            hosts=MockauSettings.elk.uri,
            max_retries=3,
            retry_on_timeout=True,
            timeout=10,
        )

        if await self.state.elasticsearch_client.ping():
            print("Elasticsearch connected successfully!")
        else:
            raise AssertionError("Connection to ElasticSearch failed!")

        self.state.httpx_clients = {
            'default': (
                httpx.AsyncClient(http1=True, http2=True, follow_redirects=True, max_redirects=20),
                HttpClientSettings(),
            ),
        }

    async def destruct_state(self):
        await self.state.elasticsearch_client.close()
        self.state.mongo_events_client.close()
        self.state.mongo_actions_client.close()
        self.state.mongo_settings_client.close()

        for client, _ in self.state.httpx_clients.values():
            await client.aclose()
