import asyncio

from elasticsearch import AsyncElasticsearch

from core.http.events.documents.http_request_action_event_document import HttpRequestActionEventDocument
from core.http.events.documents.http_request_error_event_document import HttpRequestErrorEventDocument
from core.http.events.documents.http_request_event_document import HttpRequestEventDocument
from core.http.events.documents.http_request_response_view_event_document import HttpRequestResponseViewEventDocument
from core.http.events.documents.http_response_event_document import HttpResponseEventDocument


async def init_elasticsearch_documents(using: AsyncElasticsearch) -> None:
    tasks = [
        HttpRequestResponseViewEventDocument.init(using=using),
        HttpResponseEventDocument.init(using=using),
        HttpRequestActionEventDocument.init(using=using),
        HttpRequestErrorEventDocument.init(using=using),
        HttpRequestEventDocument.init(using=using),
    ]
    await asyncio.gather(*tasks)
