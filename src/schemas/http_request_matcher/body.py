from typing import Literal

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.http_request.http_parts import HttpContentType


class BodyMatcher(AbstractMatcher):
    type_of: HttpContentType


class ObjectMatcher(AbstractMatcher):
    nested_object: dict | list


class JsonContentMatcher(BodyMatcher):
    type_of: Literal['JSON']
