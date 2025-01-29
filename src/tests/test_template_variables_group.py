import pytest

from schemas.common_variables import PlainVariable, TemplateVariablesGroup


class TestTemplateVariablesGroup:
    @pytest.mark.parametrize(
        argnames=['template', 'value', 'expected_result'],
        argvalues=[
            ['/some/path/${variable_1}', '/some/path/hello', {'${variable_1}': 'hello'}],
            ['/some/path/${variable_1}/.+', '/some/path/hello/world', {'${variable_1}': 'hello'}],
        ],
        ids=[
            'one_variable',
            'one_variable_with_extra_regex',
        ],
    )
    def test_get_values_mapping(self, template, value, expected_result):
        template_variables = TemplateVariablesGroup(
            variables=[
                PlainVariable(variable_name='${variable_1}'),
            ],
            template=template,
        )
        assert template_variables.get_values_mapping(value) == expected_result

    @pytest.mark.parametrize(
        argnames=['template', 'value'],
        argvalues=[
            [
                '/some/path/${variable_1}',
                '/some/another/path/hello',
            ],
            [
                '/some/path/${variable_1}',
                '/some/path/hello/world',
            ],
        ],
        ids=[
            'value_is_not_matched',
            'extra_substring_after',
        ],
    )
    def test_cannot_get_values_mapping_if_value_does_not_match_to_template(self, template, value):
        template_variables = TemplateVariablesGroup(
            variables=[PlainVariable(variable_name='${variable_1}')], template=template
        )
        assert template_variables.get_values_mapping(value) is None
