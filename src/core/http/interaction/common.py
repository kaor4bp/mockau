from enum import Enum


class HttpMethod(Enum):
    GET = 'GET'
    POST = 'POST'
    PUT = 'PUT'
    DELETE = 'DELETE'
    PATCH = 'PATCH'
    HEAD = 'HEAD'
    OPTIONS = 'OPTIONS'
    TRACE = 'TRACE'


class HttpContentType(Enum):
    BINARY = 'BINARY'
    XML = 'XML'
    JSON = 'JSON'
    TEXT = 'TEXT'
    EMPTY = 'EMPTY'
