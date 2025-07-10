from pydantic import Field

from core.deprecated_matchers.abstract_matcher import AbstractMatcher
from core.deprecated_matchers.string_matcher import t_StringMatcher
from core.http.interaction.schemas import HttpQueryParam
from core.predicates import t_Predicate
from core.predicates.collections.object_predicates import ObjectEqualTo
from core.predicates.logical.logical_predicates import AndPredicate, OrPredicate
from schemas.variables import VariablesContext, variables_context_transaction


class QueryParamItemMatcher(AbstractMatcher):
    key: t_StringMatcher
    value: t_StringMatcher | None = Field(default=None)

    @variables_context_transaction
    def is_matched(self, values: list[HttpQueryParam], *, context: VariablesContext) -> bool:
        for param in values:
            if not self.key.is_matched(param.key, context=context):
                continue

            if self.value:
                return self.value.is_matched(param.value, context=context)
            else:
                return True
        else:
            return False

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        object_plain_matcher = {'key': self.key.to_predicate(context=context)}
        if self.value:
            object_plain_matcher['value'] = self.value.to_predicate(context=context)
        return ObjectEqualTo(value=object_plain_matcher)


class QueryParamAndMatcher(AbstractMatcher):
    all_of: list['t_QueryParamMatcherContainer']

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        return AndPredicate(predicates=[matcher.to_predicate(context=context) for matcher in self.all_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.all_of:
            if not item.is_matched(value, context=context):
                return False
        return True


class QueryParamOrMatcher(AbstractMatcher):
    any_of: list['t_QueryParamMatcherContainer']

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        return OrPredicate(predicates=[matcher.to_predicate(context=context) for matcher in self.any_of])

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        for item in self.any_of:
            if item.is_matched(value, context=context):
                return True
        return False


t_QueryParamMatcherContainer = QueryParamAndMatcher | QueryParamOrMatcher | QueryParamItemMatcher
