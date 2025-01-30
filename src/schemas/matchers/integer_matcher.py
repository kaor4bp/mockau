from schemas.matchers.abstract_matcher import AbstractMatcher
from schemas.variables_context import VariablesContext, variables_context_transaction


class IntegerMatcher(AbstractMatcher):
    equal_to: int | None = None
    gte: int | None = None
    gt: int | None = None
    lte: int | None = None
    lt: int | None = None
    multiply_of: int | None = None

    and_: list['IntegerMatcher'] | None = None
    or_: list['IntegerMatcher'] | None = None
    not_: 'IntegerMatcher | None' = None

    @variables_context_transaction
    def is_matched(self, value: int, *, context: VariablesContext) -> bool:
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.gte is not None and value < self.gte:
            return False
        if self.gt is not None and value <= self.gt:
            return False
        if self.lte is not None and value > self.lte:
            return False
        if self.lt is not None and value >= self.lt:
            return False
        if self.multiply_of is not None and value % self.multiply_of != 0:
            return False
        if self.and_ and any(not item.is_matched(value, context=context) for item in self.and_):
            return False
        if self.or_ and all(not item.is_matched(value, context=context) for item in self.or_):
            return False
        if self.not_ and self.not_.is_matched(value, context=context):
            return False
        return True


t_IntegerMatcher = IntegerMatcher
