import logging
import pathlib
from contextlib import asynccontextmanager
from datetime import datetime, timedelta

import pytz
import uvicorn
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from fastapi import BackgroundTasks, FastAPI, Request
from starlette.responses import JSONResponse

from admin.router import admin_debug_router, admin_router
from models.storable_settings import DynamicEntrypoint
from processor.background_tasks import cleanup_events, group_events
from processor.processor_pipeline import HttpProcessorPipeline
from schemas import HttpRequest


def add_dynamic_entrypoint(app: FastAPI, name: str) -> None:
    for method in ['GET', 'POST', 'HEAD', 'PATCH', 'PUT', 'DELETE']:
        app.add_api_route(
            path=f'/{name}{{full_path:path}}',
            endpoint=generate_dynamic_router_processor(name),
            tags=[f'Dynamic Entrypoint {name}'],
            methods=[method],
            operation_id=f'dynamic_entrypoint_{method}_{name}',
        )
        app.routes.insert(-1, app.routes.pop())


@asynccontextmanager
async def lifespan(app: FastAPI):
    for de in await DynamicEntrypoint.get_all():
        add_dynamic_entrypoint(app, de.name)

    scheduler = AsyncIOScheduler()
    scheduler.add_job(
        group_events,
        'interval',
        seconds=timedelta(minutes=1).total_seconds(),
        max_instances=1,
        next_run_time=datetime.now(tz=pytz.UTC),
    )
    scheduler.add_job(
        cleanup_events,
        'interval',
        seconds=timedelta(minutes=30).total_seconds(),
        max_instances=1,
        next_run_time=datetime.now(tz=pytz.UTC),
    )
    scheduler.start()
    yield
    scheduler.shutdown(wait=True)


app = FastAPI(lifespan=lifespan)
app.include_router(admin_router)
app.include_router(admin_debug_router)


def generate_dynamic_router_processor(name: str):
    async def dynamic_router_processor(request: Request, background_tasks: BackgroundTasks):
        http_request = await HttpRequest.from_fastapi_request(request)

        pipeline = HttpProcessorPipeline(http_request, entrypoint=name)
        response = await pipeline.run()

        if response:
            return response.to_fastapi_response()
        else:
            return JSONResponse(
                content={'error': f'not found in entrypoint "{name}"'},
                status_code=response.status_code if response else 404,
            )

    return dynamic_router_processor


@app.post("/mockau/admin/create_entrypoint", tags=['Admin'])
async def create_entrypoint(name: str):
    if name in ['default', 'mockau']:
        return JSONResponse(
            content={'status': 'name is forbidden'},
            status_code=403,
        )

    de = DynamicEntrypoint(name=name)
    if await de.exists():
        return JSONResponse(
            content={'status': 'already exists'},
            status_code=409,
        )
    await de.create()
    add_dynamic_entrypoint(app, de.name)
    return JSONResponse(
        content={'status': 'done'},
        status_code=200,
    )


@app.get("/{full_path:path}", tags=['Default Entrypoint'])
@app.post("/{full_path:path}", tags=['Default Entrypoint'])
@app.patch("/{full_path:path}", tags=['Default Entrypoint'])
@app.put("/{full_path:path}", tags=['Default Entrypoint'])
@app.delete("/{full_path:path}", tags=['Default Entrypoint'])
@app.head("/{full_path:path}", tags=['Default Entrypoint'])
async def default_dynamic_router(full_path, request: Request, background_tasks: BackgroundTasks):
    http_request = await HttpRequest.from_fastapi_request(request)

    pipeline = HttpProcessorPipeline(http_request)
    response = await pipeline.run()

    if response:
        return response.to_fastapi_response()
    else:
        return JSONResponse(
            content={'error': 'not found'},
            status_code=response.status_code if response else 404,
        )


if __name__ == "__main__":
    cwd = pathlib.Path(__file__).parent.resolve()
    uvicorn.run(app, host="127.0.0.1", port=8000, log_level=logging.INFO)
