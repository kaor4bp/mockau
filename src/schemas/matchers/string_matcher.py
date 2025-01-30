import re
from typing import Annotated, Optional

from pydantic import Field

from schemas.matchers.abstract_matcher import AbstractMatcher
from schemas.matchers.integer_matcher import t_IntegerMatcher
from schemas.variables import t_VariableMatcher
from schemas.variables_context import VariablesContext, variables_context_transaction


class StringMatcher(AbstractMatcher):
    variable: t_VariableMatcher | None = None
    pattern: str | None = None
    equal_to: str | None = None
    contains: str | None = None
    length: Optional[t_IntegerMatcher] = None

    and_: Annotated[
        list['StringMatcher'] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'foobar'}, {'contains': 'bar'}],
                [{'pattern': 'bar'}],
            ],
        ),
    ]
    or_: Annotated[
        list['StringMatcher'] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'foo'}, {'equal_to': 'bar'}],
                [{'pattern': 'bar'}],
            ],
        ),
    ]
    not_: Annotated[
        Optional['StringMatcher'],
        Field(
            default=None,
            examples=[
                {'equal_to': 'foo'},
                {'pattern': 'bar'},
                {'contains': 'bar'},
            ],
        ),
    ]

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if self.variable is not None and not self.variable.is_matched(value, context=context):
            return False
        if self.pattern is not None and not re.fullmatch(self.pattern, value):
            return False
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.contains is not None and self.contains not in value:
            return False
        if self.length is not None and not self.length.is_matched(len(value), context=context):
            return False
        if self.and_ is not None and any(not item.is_matched(value, context=context) for item in self.and_):
            return False
        if self.or_ is not None and all(not item.is_matched(value, context=context) for item in self.or_):
            return False
        if self.not_ is not None and self.not_.is_matched(value, context=context):
            return False
        return True


t_StringMatcher = Annotated[
    StringMatcher,
    Field(
        examples=[
            {'not_': {'equal_to': 'foo'}},
            {'contains': 'bar'},
            {'any_of': [{'equal_to': 'foo'}, {'equal_to': 'bar'}]},
            {'contains': 'bar', 'not_': {'equal_to': 'foobar'}},
        ]
    ),
]
