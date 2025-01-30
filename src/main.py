import logging
import pathlib
from contextlib import asynccontextmanager

import uvicorn
from fastapi import BackgroundTasks, FastAPI, Request
from starlette.responses import JSONResponse
from starlette.routing import Route

from admin.router import admin_router
from models.storable_settings import DynamicEntrypoint
from processor.background_tasks import group_events
from processor.processor_pipeline import HttpProcessorPipeline
from schemas import HttpRequest


@asynccontextmanager
async def lifespan(app: FastAPI):
    for de in await DynamicEntrypoint.get_all():
        route = Route(f'/{de.name}{{full_path:path}}', generate_dynamic_router_processor(de.name))
        app.routes.insert(0, route)

    yield


app = FastAPI(lifespan=lifespan)
app.include_router(admin_router)


def generate_dynamic_router_processor(name: str):
    async def dynamic_router_processor(request: Request):
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
    route = Route(f'/{name}{{full_path:path}}', generate_dynamic_router_processor(name))
    app.routes.insert(0, route)
    return JSONResponse(
        content={'status': 'done'},
        status_code=200,
    )


@app.get("/{full_path:path}", tags=['Default Dynamic Router'])
@app.post("/{full_path:path}", tags=['Default Dynamic Router'])
@app.patch("/{full_path:path}", tags=['Default Dynamic Router'])
@app.put("/{full_path:path}", tags=['Default Dynamic Router'])
@app.delete("/{full_path:path}", tags=['Default Dynamic Router'])
@app.head("/{full_path:path}", tags=['Default Dynamic Router'])
async def default_dynamic_router(full_path, request: Request, background_tasks: BackgroundTasks):
    background_tasks.add_task(group_events)
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
