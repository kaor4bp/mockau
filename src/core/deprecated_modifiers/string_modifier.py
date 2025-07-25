import re
from typing import Annotated

from pydantic import Field

from core.deprecated_modifiers.abstract_modifier import AbstractModifier
from schemas.variables import VariablesContext


class StringModifier(AbstractModifier):
    remove_suffix: str | None = None
    remove_prefix: str | None = None

    replace_regex: str | None = None
    replace: str | None = None
    replace_with: str | None = None

    and_: Annotated[
        list['StringModifier'] | None,
        Field(
            default=None,
            examples=[
                [{'remove_suffix': 'foobar'}],
                [{'replace': 'foo', 'replace_with': 'bar'}],
            ],
        ),
    ]

    def modify(self, value: str, *, context: VariablesContext) -> str:
        if self.remove_suffix is not None:
            value = value.removesuffix(context.apply_variables(self.remove_suffix))
        if self.remove_prefix is not None:
            value = value.removeprefix(context.apply_variables(self.remove_prefix))
        if self.replace_regex is not None:
            value = re.sub(
                context.apply_variables(self.replace_regex),
                context.apply_variables(self.replace_with or ''),
                value,
            )
        if self.replace is not None:
            value = value.replace(
                context.apply_variables(self.replace),
                context.apply_variables(self.replace_with or ''),
            )
        if self.and_ is not None:
            for modifier in self.and_:
                value = modifier.modify(value, context=context)
        return value
