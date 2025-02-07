import re
from typing import Annotated, Optional

from pydantic import Field

from core.matchers.variable_matcher import SetVariableMatcher
from core.plain_matchers.common_plain_matchers import And, Any, Not, Or
from core.plain_matchers.string_plain_matchers import StringContains, StringEqualTo, StringPattern
from schemas.variables import VariablesContext, variables_context_transaction


class StringMatcher(SetVariableMatcher):
    pattern: str | None = None
    equal_to: str | None = None
    contains: str | None = None

    and_: Annotated[
        list['StringMatcher'] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'foobar'}, {'contains': 'bar'}],
                [{'set_variable': 'bar'}],
            ],
        ),
    ]
    or_: Annotated[
        list['StringMatcher'] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'foo'}, {'equal_to': 'bar'}],
                [{'set_variable': 'bar'}],
            ],
        ),
    ]
    not_: Annotated[
        Optional['StringMatcher'],
        Field(
            default=None,
            examples=[
                {'equal_to': 'foo'},
                {'set_variable': 'bar'},
                {'contains': 'bar'},
            ],
        ),
    ]

    def to_plain_matcher(self, *, context: VariablesContext):
        plain_matchers = []

        if self.pattern is not None:
            plain_matchers.append(StringPattern(self.pattern))
        if self.equal_to is not None:
            plain_matchers.append(StringEqualTo(self.equal_to))
        if self.contains is not None:
            plain_matchers.append(StringContains(self.contains))
        if self.and_ is not None:
            plain_matchers.append(And(*[matcher.to_plain_matcher(context=context) for matcher in self.and_]))
        if self.or_ is not None:
            plain_matchers.append(Or(*[matcher.to_plain_matcher(context=context) for matcher in self.and_]))
        if self.not_ is not None:
            plain_matchers.append(Not(self.not_.to_plain_matcher(context=context)))
        if self.set_variable is not None:
            plain_matchers.append(super().to_plain_matcher(context=context))

        if len(plain_matchers) == 0:
            return Any()
        elif len(plain_matchers) == 1:
            return plain_matchers[0]
        else:
            return And(*plain_matchers)

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if self.pattern is not None and not re.fullmatch(self.pattern, value):
            return False
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.contains is not None and self.contains not in value:
            return False
        if self.and_ is not None and any(not item.is_matched(value, context=context) for item in self.and_):
            return False
        if self.or_ is not None and all(not item.is_matched(value, context=context) for item in self.or_):
            return False
        if self.not_ is not None and self.not_.is_matched(value, context=context):
            return False
        if self.set_variable is not None and not self.is_variable_matched(value, context=context):
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
