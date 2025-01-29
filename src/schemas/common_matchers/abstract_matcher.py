from abc import abstractmethod
from typing import TypeVar

from black.nodes import Generic

from schemas.base_schema import BaseSchema


class AbstractMatcher(BaseSchema):
    @abstractmethod
    def is_matched(self, value) -> bool:
        pass


t_Matcher = TypeVar('t_Matcher', bound=AbstractMatcher)


class AndMatcher(AbstractMatcher, Generic[t_Matcher]):
    and_: list[t_Matcher]

    def is_matched(self, value) -> bool:
        for item in self.and_:
            if not item.is_matched(value):
                return False
        return True


class OrMatcher(AbstractMatcher, Generic[t_Matcher]):
    or_: list[t_Matcher]

    def is_matched(self, value) -> bool:
        for item in self.or_:
            if item.is_matched(value):
                return True
        return False
