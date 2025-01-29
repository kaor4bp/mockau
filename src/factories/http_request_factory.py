from polyfactory.factories.pydantic_factory import ModelFactory

from schemas.http_request import HttpRequest


class HttpRequestFactory(ModelFactory[HttpRequest]):
    __model__ = HttpRequest
