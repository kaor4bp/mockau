from polyfactory.factories.pydantic_factory import ModelFactory

from core.http.interaction.schemas import HttpRequest


class HttpRequestFactory(ModelFactory[HttpRequest]):
    __model__ = HttpRequest
