import re

from pydantic import Field

from core.matchers.abstract_matcher import AbstractMatcher
from core.predicates.base_predicate import t_Predicate
from core.predicates.logical.logical_predicates import AnyPredicate
from core.predicates.scalars import StringPattern
from schemas.variables import VariablesContext, variables_context_transaction
from utils.string_utils import split_string


class SetVariableMatcher(AbstractMatcher):
    set_variable: str | None = Field(default=None, examples=['/some/path/${variable_1}/.*'])

    def __hash__(self):
        return self.model_dump_json().__hash__()

    def to_predicate(self, *, context: VariablesContext) -> t_Predicate:
        variable_names = re.findall(r'\${\w+}', self.set_variable)

        if not variable_names:
            return AnyPredicate()

        pattern = self.set_variable
        for variable_name in variable_names:
            var_regex = self._get_variable_regex(variable_name, context=context)
            pattern = pattern.replace(variable_name, var_regex)

        return StringPattern(pattern=pattern)

    def _get_variable_regex(self, variable_name: str, context: VariablesContext) -> str:
        for variable in context.variables_group.variables:
            if variable.name == variable_name:
                return variable.pattern
        return '.+'

    def _quick_is_match(self, value: str, context: VariablesContext) -> bool:
        variable_names = re.findall(r'\${\w+}', self.set_variable)

        pattern = self.set_variable
        for variable_name in variable_names:
            var_regex = self._get_variable_regex(variable_name, context=context)
            pattern = pattern.replace(variable_name, var_regex)
        return bool(re.fullmatch(pattern, value))

    @variables_context_transaction
    def is_variable_matched(self, value: str, *, context: VariablesContext) -> bool:
        return SetVariableMatcher.is_matched(self, value, context=context)

    @variables_context_transaction
    def is_matched(self, value: str, *, context: VariablesContext) -> bool:
        value = str(value)
        if not self._quick_is_match(value, context=context):
            return False

        variable_names = re.findall(r'\${\w+}', self.set_variable)
        if not variable_names:
            return True

        variables_regexes_mapping = {}
        for variable_name in variable_names:
            variables_regexes_mapping[variable_name] = self._get_variable_regex(variable_name, context)

        pattern_chunks = []
        pattern = self.set_variable
        for variable_name in variable_names:
            before_regex, pattern = pattern.split(variable_name, maxsplit=1)
            pattern_chunks.append(before_regex)
            pattern_chunks.append(variables_regexes_mapping[variable_name])
        pattern_chunks.append(pattern)

        for variant_chunks in split_string(value, len(variable_names) * 2 + 1):
            is_success = True
            checkers = [item for item in zip(pattern_chunks, variant_chunks)]
            checkers.sort(key=lambda x: len(x[0]), reverse=False)
            for regex_pattern, value_part in checkers:
                if not re.fullmatch(regex_pattern, value_part):
                    is_success = False
                    break
            if not is_success:
                continue

            for variable_name, variable_value in zip(variable_names, variant_chunks[1 : len(variant_chunks) + 1 : 2]):
                if not context.set(variable_name, variable_value):
                    is_success = False
                    break

            if not is_success:
                continue
            else:
                return True

        return False
