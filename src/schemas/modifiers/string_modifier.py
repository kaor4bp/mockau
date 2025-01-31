import re
from enum import Enum
from typing import Annotated, Union

from pydantic import Field

from schemas.modifiers.abstract_modifier import AbstractModifier


class StringReplaceModifier(AbstractModifier):
    old: str
    new: str

    def modify(self, value: str) -> str:
        return value.replace(self.old, self.new)


class StringToConstantModifier(AbstractModifier):
    to_value: str

    def modify(self, value: str) -> str:
        return self.to_value


class StringRegexSubModifier(AbstractModifier):
    pattern: str
    repl: str

    def modify(self, value: str) -> str:
        return re.sub(self.pattern, self.repl, value)


class StringCase(Enum):
    LOWER = 'LOWER'
    UPPER = 'UPPER'
    CAPITALIZED = 'CAPITALIZED'


class StringCaseModifier(AbstractModifier):
    case_to: StringCase

    def modify(self, value: str) -> str:
        if self.case_to is StringCase.LOWER:
            return value.lower()
        elif self.case_to is StringCase.UPPER:
            return value.upper()
        elif self.case_to is StringCase.CAPITALIZED:
            return value.capitalize()
        else:
            raise NotImplementedError(f'StringCase type {self.case_to} is not implemented yet')


class RegexSubstringsModifier(AbstractModifier):
    pattern: str
    modifier: 't_StringModifier'

    def modify(self, value: str) -> str:
        matches = re.findall(self.pattern, value)
        for match in matches:
            value = value.replace(match, self.modifier.modify(match))
        return value


class IndexSubstringsModifier(AbstractModifier):
    from_: int | None = None
    to: int | None = None
    modifier: 't_StringModifier'

    def modify(self, value: str) -> str:
        if self.from_ is not None and self.to is None:
            substring = value[self.from_ : :]
        elif self.from_ is None and self.to is not None:
            substring = value[: self.to]
        elif self.from_ is not None and self.to is not None:
            substring = value[self.from_ : self.to]
        else:
            substring = value
        return value.replace(substring, self.modifier.modify(substring))


class StringAndModifier(AbstractModifier):
    and_: list['t_StringModifier']

    def modify(self, value: str) -> str:
        for modifier in self.and_:
            value = modifier.modify(value)
        return value


t_StringModifier = Annotated[
    Union[
        StringAndModifier,
        StringReplaceModifier,
        StringRegexSubModifier,
        StringCaseModifier,
        RegexSubstringsModifier,
        IndexSubstringsModifier,
        StringToConstantModifier,
    ],
    Field(examples=[{'and_': [{'set_variable': '/test-env-d+/', 'modifier': {'old': 'test', 'new': 'staging'}}]}]),
]
