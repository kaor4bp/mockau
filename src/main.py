import logging
import pathlib
from contextlib import asynccontextmanager

import uvicorn
from fastapi import BackgroundTasks, FastAPI, Request
from starlette.responses import JSONResponse

from admin.router import admin_debug_router, admin_router
from core.http.interaction.schemas import HttpRequest
from core.http.processor.http_processor_pipeline import HttpProcessorPipeline
from core.init_elasticsearch_documents import init_elasticsearch_documents
from mockau_fastapi import MockauFastAPI
from models.storable_settings import DynamicEntrypoint


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
async def lifespan(app: MockauFastAPI):
    await app.init_state()
    await init_elasticsearch_documents(app.state.clients.elasticsearch_client)

    for de in await DynamicEntrypoint.get_all(app.state.clients):
        add_dynamic_entrypoint(app, de.name)

    #     query = (
    #         app.state.clients.mongo_actions_client.find(filters={'entrypoint': de.name, 'active': True})
    #         .sort({'priority': -1})
    #         .batch_size(100)
    #     )
    #     actions = []
    #     async for document in query:
    #         actions.append(TypeAdapter(t_HttpActionModel).validate_python(document))
    #     print(f'Verify HttpActions consistency of "{de.name}"')
    #     verify_http_actions_consistency(actions)
    #
    # query = (
    #     app.state.clients.mongo_actions_client.find(filters={'entrypoint': 'default', 'active': True})
    #     .sort({'priority': -1})
    #     .batch_size(100)
    # )
    # actions = []
    # async for document in query:
    #     actions.append(TypeAdapter(t_HttpActionModel).validate_python(document))
    # print(f'Verify HttpActions consistency of "default"')
    # verify_http_actions_consistency(actions)

    # scheduler = AsyncIOScheduler()
    # scheduler.start()
    yield
    # scheduler.shutdown(wait=True)
    await app.destruct_state()


app = MockauFastAPI(lifespan=lifespan)
app.include_router(admin_router)
app.include_router(admin_debug_router)


def generate_dynamic_router_processor(name: str):
    async def dynamic_router_processor(request: Request, background_tasks: BackgroundTasks):
        request.state.body = await request.body()
        http_request = await HttpRequest.from_fastapi_request(request)

        pipeline = HttpProcessorPipeline(
            app=request.app,
            background_tasks=background_tasks,
            http_request=http_request,
            entrypoint=name,
        )
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
async def create_entrypoint(name: str, request: Request):
    local_app: MockauFastAPI = request.app

    if name in ['default', 'mockau']:
        return JSONResponse(
            content={'status': 'name is forbidden'},
            status_code=403,
        )

    de = DynamicEntrypoint(name=name)
    if await de.exists(local_app.state.clients):
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
async def default_dynamic_router(
    request: Request,
    background_tasks: BackgroundTasks,
):
    request.state.body = await request.body()
    http_request = await HttpRequest.from_fastapi_request(request)

    pipeline = HttpProcessorPipeline(
        app=request.app,
        background_tasks=background_tasks,
        http_request=http_request,
    )
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
    uvicorn.run('main:app', host="127.0.0.1", port=8000, log_level=logging.INFO, workers=1)
