import logging
import pathlib

import uvicorn
from fastapi import FastAPI, Request
from starlette.responses import JSONResponse

from admin.router import admin_router
from processor.processor_pipeline import HttpProcessorPipeline
from schemas import HttpRequest

app = FastAPI()
app.include_router(admin_router)


@app.exception_handler(404)
async def handler_404_redirect(request: Request, __):
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
