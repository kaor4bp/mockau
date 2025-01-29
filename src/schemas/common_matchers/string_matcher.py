import re
from typing import Annotated, Optional

from pydantic import Field

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.common_matchers.integer_matcher import t_IntegerMatcher


class StringMatcher(AbstractMatcher):
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

    def is_matched(self, value) -> bool:
        if self.pattern is not None and not re.fullmatch(self.pattern, value):
            return False
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.contains is not None and self.contains not in value:
            return False
        if self.length is not None and not self.length.is_matched(len(value)):
            return False
        if self.and_ is not None and any(not item.is_matched(value) for item in self.and_):
            return False
        if self.or_ is not None and all(not item.is_matched(value) for item in self.or_):
            return False
        if self.not_ is not None and self.not_.is_matched(value):
            return False
        return True


t_StringMatcher = Annotated[
    StringMatcher,
    Field(
        examples=[
            {'not_': {'equal_to': 'foo'}},
            {'contains': 'bar'},
            {'or_': [{'equal_to': 'foo'}, {'equal_to': 'bar'}]},
            {'contains': 'bar', 'not_': {'equal_to': 'foobar'}},
        ]
    ),
]
