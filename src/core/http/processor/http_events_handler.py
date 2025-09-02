import asyncio
import time
from asyncio import create_task

from fastapi import BackgroundTasks
from minow_fastapi import MockauFastAPI

from core.http.actions.common import ActionReference
from core.http.actions.types import t_HttpActionModel
from core.http.events.common import HttpEventType
from core.http.events.documents import (
    HttpRequestActionEventDocument,
    HttpRequestErrorEventDocument,
    HttpRequestEventDocument,
    HttpResponseEventDocument,
)
from core.http.events.documents.http_request_action_not_matched_view_event_document import (
    HttpRequestActionNotMatchedViewEventDocument,
)
from core.http.events.documents.http_request_response_view_event_document import HttpRequestResponseViewEventDocument
from core.http.events.models import (
    HttpRequestActionEventModel,
    HttpRequestActionNotMatchedViewEventModel,
    HttpRequestErrorEventModel,
    HttpRequestEventModel,
    HttpResponseEventModel,
)
from core.http.events.models.http_request_response_view_event_model import HttpRequestResponseViewEventModel
from core.http.interaction.schemas import HttpRequest
from core.http.interaction.schemas.http_response import HttpResponse


class HttpEventsHandler:
    def __init__(
        self,
        app: MockauFastAPI,
        background_tasks: BackgroundTasks,
        inbound_http_request: HttpRequest,
        time_start: float,
    ) -> None:
        self.tasks = []
        self.app = app
        self.background_tasks = background_tasks
        self.inbound_http_request = inbound_http_request
        self.time_start = time_start

    async def submit(self):
        await asyncio.gather(*self.tasks)
        self.tasks.clear()

    async def on_inbound_request_received(self):
        event = HttpRequestEventModel(
            event=(
                HttpEventType.HTTP_EXTERNAL_REQUEST
                if self.inbound_http_request.is_external
                else HttpEventType.HTTP_TRANSIT_REQUEST
            ),
            http_request=self.inbound_http_request,
            minow_traceparent=self.inbound_http_request.minow_traceparent,
            traceparent=self.inbound_http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestEventDocument.from_model(event).save(using=self.app.state.task_clients.elasticsearch_client)
            )
        )

    async def on_too_many_redirects_error(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_REQUEST_TOO_MANY_REDIRECTS.value,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )

    async def on_action_is_matched(self, action: t_HttpActionModel):
        event = HttpRequestActionEventModel(
            event=HttpEventType.HTTP_REQUEST_ACTION_MATCHED.value,
            minow_traceparent=self.inbound_http_request.minow_traceparent,
            action_reference=ActionReference(
                action_id=action.id,
                action_revision=action.revision,
            ),
            traceparent=self.inbound_http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestActionEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )

    async def on_actions_mismatched(self):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_REQUEST_NO_ACTION_FOUND.value,
            minow_traceparent=self.inbound_http_request.minow_traceparent,
            traceparent=self.inbound_http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            ),
        )

    async def on_request_send(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST,
            minow_traceparent=http_request.minow_traceparent,
            http_request=http_request,
            traceparent=self.inbound_http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestEventDocument.from_model(event).save(using=self.app.state.task_clients.elasticsearch_client)
            ),
        )

    async def on_response_received(
        self,
        minow_traceparent: str,
        http_response: HttpResponse,
    ):
        event = HttpResponseEventModel(
            event=HttpEventType.HTTP_RECEIVED_RESPONSE,
            minow_traceparent=minow_traceparent,
            http_response=http_response,
            traceparent=self.inbound_http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpResponseEventDocument.from_model(event).save(using=self.app.state.task_clients.elasticsearch_client)
            ),
        )

    async def on_request_response_view_event(self, http_request: HttpRequest, http_response: HttpResponse | None):
        event = HttpRequestResponseViewEventModel(
            event=(
                HttpEventType.HTTP_EXTERNAL_REQUEST_RESPONSE_VIEW.value
                if http_request.is_external
                else HttpEventType.HTTP_INTERNAL_REQUEST_RESPONSE_VIEW.value
            ),
            http_request=http_request,
            http_response=http_response,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
            elapsed=time.monotonic() - self.time_start,
            processing_time=time.monotonic() - self.time_start - (http_response.elapsed if http_response else 0),
        )
        self.tasks.append(
            create_task(
                HttpRequestResponseViewEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            ),
        )

    async def on_action_mismatched_event(self, action: t_HttpActionModel, description: str):
        lazy_event = HttpRequestActionNotMatchedViewEventModel(
            event=HttpEventType.HTTP_ACTION_NOT_MATCHED_VIEW.value,
            minow_traceparent=self.inbound_http_request.minow_traceparent,
            action_reference=ActionReference(
                action_id=action.id,
                action_revision=action.revision,
            ),
            description=description,
            traceparent=self.inbound_http_request.traceparent,
        )
        lazy_event_doc = HttpRequestActionNotMatchedViewEventDocument.from_model(lazy_event)
        self.background_tasks.add_task(
            lazy_event_doc.save,
            using=self.app.state.background_clients.elasticsearch_client,
        )

    async def on_send_request_read_timeout(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST_READ_TIMEOUT.value,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )

    async def on_send_request_connect_timeout(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST_CONNECT_TIMEOUT.value,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )

    async def on_send_request_pool_timeout(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST_POOL_TIMEOUT.value,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )

    async def on_send_request_write_timeout(
        self,
        http_request: HttpRequest,
    ):
        event = HttpRequestErrorEventModel(
            event=HttpEventType.HTTP_SEND_REQUEST_WRITE_TIMEOUT.value,
            minow_traceparent=http_request.minow_traceparent,
            traceparent=http_request.traceparent,
        )
        self.tasks.append(
            create_task(
                HttpRequestErrorEventDocument.from_model(event).save(
                    using=self.app.state.task_clients.elasticsearch_client
                )
            )
        )
