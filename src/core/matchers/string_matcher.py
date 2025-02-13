import re
from typing import Annotated, Optional

from pydantic import Field

from core.matchers.variable_matcher import SetVariableMatcher
from core.plain_matchers.string_plain_matchers import (
    StringAnd,
    StringAny,
    StringContains,
    StringEqualTo,
    StringNot,
    StringOr,
    StringPattern,
)
from schemas.variables import VariablesContext, variables_context_transaction


class StringMatcher(SetVariableMatcher):
    pattern: str | None = None
    equal_to: str | None = None
    startswith: str | None = None
    endswith: str | None = None
    contains: str | None = None
    ignore_case: bool = False

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
            plain_matchers.append(StringPattern(pattern=self.pattern, ignore_case=self.ignore_case))
        if self.equal_to is not None:
            plain_matchers.append(StringEqualTo(value=self.equal_to, ignore_case=self.ignore_case))
        if self.contains is not None:
            plain_matchers.append(StringContains(value=self.contains, ignore_case=self.ignore_case))
        if self.startswith is not None:
            plain_matchers.append(StringPattern(pattern=f'{self.startswith}.*', ignore_case=self.ignore_case))
        if self.endswith is not None:
            plain_matchers.append(StringPattern(pattern=f'.*{self.endswith}', ignore_case=self.ignore_case))
        if self.and_ is not None:
            plain_matchers.append(
                StringAnd(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.and_])
            )
        if self.or_ is not None:
            plain_matchers.append(
                StringOr(matchers=[matcher.to_plain_matcher(context=context) for matcher in self.and_])
            )
        if self.not_ is not None:
            plain_matchers.append(StringNot(matcher=self.not_.to_plain_matcher(context=context)))
        if self.set_variable is not None:
            plain_matchers.append(super().to_plain_matcher(context=context))

        if len(plain_matchers) == 0:
            return StringAny()
        elif len(plain_matchers) == 1:
            return plain_matchers[0]
        else:
            return StringAnd(matchers=plain_matchers)

    @variables_context_transaction
    def is_matched(self, value, *, context: VariablesContext) -> bool:
        if self.ignore_case:
            value = value.lower()

        if self.pattern is not None and not re.fullmatch(
            self.pattern, value, flags=re.IGNORECASE if self.ignore_case else 0
        ):
            return False

        if self.ignore_case:
            if self.equal_to is not None and self.equal_to.lower() != value:
                return False
            if self.contains is not None and self.contains.lower() not in value:
                return False
            if self.startswith is not None and not value.lower().startswith(self.startswith.lower()):
                return False
            if self.endswith is not None and not value.lower().endswith(self.endswith.lower()):
                return False
        else:
            if self.equal_to is not None and self.equal_to != value:
                return False
            if self.contains is not None and self.contains not in value:
                return False
            if self.startswith is not None and not value.startswith(self.startswith):
                return False
            if self.endswith is not None and not value.endswith(self.endswith):
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
