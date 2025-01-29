import itertools
import re
from abc import ABC, abstractmethod

from pydantic import Field

from schemas import BaseSchema
from schemas.common_matchers.abstract_matcher import AbstractMatcher


class AbstractVariable(ABC, AbstractMatcher):
    @abstractmethod
    def get_value(self, value):
        pass


class PlainVariable(AbstractVariable):
    variable_name: str

    def get_value(self, value):
        if self.is_matched(value):
            return value

    def is_matched(self, value) -> bool:
        return True


class RegexVariable(PlainVariable):
    pattern: str

    def is_matched(self, value) -> bool:
        return bool(re.fullmatch(self.pattern, value))


t_Variable = RegexVariable | PlainVariable


class TemplateVariablesGroup(BaseSchema):
    variables: list[t_Variable]
    template: str = Field(
        examples=[
            '/some/path/${variable_1}/and/${variable_2}',
        ],
    )

    def _get_variable_by_name(self, variable_name: str) -> t_Variable | None:
        for variable in self.variables:
            if variable.variable_name == variable_name:
                return variable
        return None

    def get_values_mapping(self, value: str) -> dict[str, str] | None:
        if not self.is_matched(value):
            return None

        variable_names = re.findall(r'\${\w+}', self.template)
        variables_regexes_mapping = {}
        for variable_name in variable_names:
            var = self._get_variable_by_name(variable_name)
            if isinstance(var, RegexVariable):
                variables_regexes_mapping[variable_name] = var.pattern
            else:
                variables_regexes_mapping[variable_name] = r'\w+'

        all_variants = []
        substrings = [''.join(value[i:j]) for i, j in itertools.combinations(range(len(value) + 1), 2)]

        for variable_name, variable_regex in variables_regexes_mapping.items():
            variable_variants = []
            for substring in substrings:
                if re.fullmatch(variable_regex, substring):
                    variable_variants.append(substring)
            all_variants.append(variable_variants)

        for variant in itertools.product(*all_variants):
            cur_mapping = {}
            value_variant = self.template
            for variable_name, variable_value in zip(variables_regexes_mapping.keys(), variant):
                cur_mapping[variable_name] = variable_value
                value_variant = value_variant.replace(variable_name, variable_value)
            if re.fullmatch(value_variant, value):
                return cur_mapping

    def is_matched(self, value: str) -> bool:
        variable_names = re.findall(r'\${\w+}', self.template)
        if len(variable_names) != len(self.variables):
            return False

        regex_template = self.template
        for variable_name in variable_names:
            var = self._get_variable_by_name(variable_name)
            if not var:
                return False
            elif isinstance(var, RegexVariable):
                regex_template = regex_template.replace(variable_name, var.pattern)
            else:
                regex_template = regex_template.replace(variable_name, r'\w+')
        return bool(re.fullmatch(regex_template, value))
