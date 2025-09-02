import elasticsearch
import httpx
from fastapi import FastAPI
from httpx import Timeout
from starlette.datastructures import State

from settings import MockauSettings
from utils.mongo import MongoClient


class MockauSharedClients:
    mongo_events_client: MongoClient
    mongo_actions_client: MongoClient
    mongo_settings_client: MongoClient
    mongo_tasks_client: MongoClient
    elasticsearch_client: elasticsearch.AsyncElasticsearch

    httpx_clients: dict[str, tuple[httpx.AsyncClient, 'HttpClientSettings']]  # noqa: F821

    def __init__(self) -> None:
        from core.storable_settings.models.dynamic_entrypoint import HttpClientSettings

        self.mongo_events_client = MongoClient(collection='minow_events')
        self.mongo_actions_client = MongoClient(collection='minow_actions')
        self.mongo_settings_client = MongoClient(collection='minow_settings')
        self.mongo_tasks_client = MongoClient(collection='minow_tasks')
        self.elasticsearch_client = elasticsearch.AsyncElasticsearch(
            hosts=MockauSettings.elk.uri,
            max_retries=3,
            retry_on_timeout=True,
            timeout=10,
        )

        self.httpx_clients = {
            'default': (
                httpx.AsyncClient(
                    http1=True,
                    http2=True,
                    follow_redirects=True,
                    max_redirects=20,
                    timeout=Timeout(
                        connect=30 * 60,
                        read=30 * 60,
                        write=30 * 60,
                        pool=30 * 60,
                    ),
                ),
                HttpClientSettings(),
            ),
        }

    async def start(self):
        if await self.elasticsearch_client.ping():
            print("Elasticsearch connected successfully!")
        else:
            raise AssertionError("Connection to ElasticSearch failed!")

    async def stop(self):
        await self.elasticsearch_client.close()
        self.mongo_events_client.close()
        self.mongo_actions_client.close()
        self.mongo_settings_client.close()
        self.mongo_tasks_client.close()

        for client, _ in self.httpx_clients.values():
            await client.aclose()


class MockauState(State):
    clients: MockauSharedClients
    background_clients: MockauSharedClients
    task_clients: MockauSharedClients


class MockauFastAPI(FastAPI):
    state: MockauState

    async def init_state(self):
        self.state.clients = MockauSharedClients()
        self.state.background_clients = MockauSharedClients()
        self.state.task_clients = MockauSharedClients()

        await self.state.clients.start()
        await self.state.background_clients.start()
        await self.state.task_clients.start()

    async def destruct_state(self):
        await self.state.clients.stop()
        await self.state.background_clients.stop()
        await self.state.task_clients.stop()
