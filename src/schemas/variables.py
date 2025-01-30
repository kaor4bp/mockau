import re
from abc import ABC
from typing import Any

from pydantic import Field

from schemas.matchers.abstract_matcher import AbstractMatcher
from schemas.variables_context import VariablesContext, variables_context_transaction
from utils.string_utils import split_string


class Variable(AbstractMatcher, ABC):
    name: str
    pattern: str = Field(default='.*')

    @variables_context_transaction
    def is_matched(self, value: str, *, context: VariablesContext) -> bool:
        if not bool(re.fullmatch(self.pattern, str(value))):
            return False
        if self.name not in context.keys() or context[self.name] == value:
            context[self.name] = value
            return True
        else:
            return False

    def get_from_context(self, context: VariablesContext) -> tuple[bool, Any]:
        if self.name in context.keys():
            return True, context[self.name]
        else:
            return False, None


t_Variable = Variable


class VariablesGroup(AbstractMatcher):
    pattern: str = Field(
        examples=[
            '/some/path/${variable_1}/and/${variable_2}',
        ],
    )
    variables: list[t_Variable]

    def _get_variable_by_name(self, variable_name: str) -> t_Variable | None:
        for variable in self.variables:
            if variable.name == variable_name:
                return variable
        return None

    def _quick_is_match(self, value: str) -> bool:
        value = str(value)
        variable_names = re.findall(r'\${\w+}', self.pattern)

        pattern = self.pattern
        for variable_name in variable_names:
            var = self._get_variable_by_name(variable_name)
            if not var:
                return False
            pattern = pattern.replace(variable_name, var.pattern)
        return bool(re.fullmatch(pattern, value))

    @variables_context_transaction
    def is_matched(self, value: str, *, context: VariablesContext) -> bool:
        if not self._quick_is_match(value):
            return False

        value = str(value)

        variable_names = re.findall(r'\${\w+}', self.pattern)
        variables_regexes_mapping = {}
        for variable_name in variable_names:
            var = self._get_variable_by_name(variable_name)
            variables_regexes_mapping[variable_name] = var.pattern

        pattern_chunks = []
        pattern = self.pattern
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

            cur_mapping = {}
            for variable_name, variable_value in zip(variable_names, variant_chunks[1 : len(variant_chunks) + 1 : 2]):
                existed_value = cur_mapping.get(variable_name)
                if existed_value is not None and existed_value != variable_value:
                    continue
                if variable_name in context.keys() and context[variable_name] != variable_value:
                    continue
                cur_mapping[variable_name] = variable_value
            context.update(cur_mapping)
            return True


t_VariableMatcher = Variable | VariablesGroup
