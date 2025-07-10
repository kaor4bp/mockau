from typing import Literal

from core.deprecated_matchers.abstract_matcher import AbstractMatcher
from core.http.interaction.common import HttpContentType


class BodyMatcher(AbstractMatcher):
    type_of: HttpContentType


class ObjectMatcher(AbstractMatcher):
    nested_object: dict | list


class JsonContentMatcher(BodyMatcher):
    type_of: Literal['JSON']
