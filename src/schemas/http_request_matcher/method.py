from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.http_request.http_parts import HttpMethod


class MethodOrMatcher(AbstractMatcher):
    any_of: list[HttpMethod]

    def is_matched(self, value) -> bool:
        return value in self.any_of


class MethodEqualToMatcher(AbstractMatcher):
    equal_to: HttpMethod

    def is_matched(self, value) -> bool:
        return self.equal_to == value


t_MethodMatcher = MethodOrMatcher | MethodEqualToMatcher
