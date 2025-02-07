from typing import Literal

from core.http.interaction.common import HttpContentType
from core.matchers.abstract_matcher import AbstractMatcher


class BodyMatcher(AbstractMatcher):
    type_of: HttpContentType


class ObjectMatcher(AbstractMatcher):
    nested_object: dict | list


class JsonContentMatcher(BodyMatcher):
    type_of: Literal['JSON']
