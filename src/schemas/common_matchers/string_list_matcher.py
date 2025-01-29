from typing import Annotated

from pydantic import Field

from schemas.common_matchers.abstract_matcher import AbstractMatcher
from schemas.common_matchers.string_matcher import t_StringMatcher


class StringListMatcher(AbstractMatcher):
    any_of: Annotated[
        list[t_StringMatcher] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'json'}],
                [{'equal_to': 'xml'}],
            ],
        ),
    ]
    one_of: Annotated[
        list[t_StringMatcher] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'json'}],
                [{'equal_to': 'xml'}],
            ],
        ),
    ]
    all_of: Annotated[
        list[t_StringMatcher] | None,
        Field(
            default=None,
            examples=[
                [{'equal_to': 'json'}],
                [{'equal_to': 'xml'}],
            ],
        ),
    ]

    and_: Annotated[list['StringListMatcher'] | None, Field(default=None, examples=[])]
    or_: Annotated[list['StringListMatcher'] | None, Field(default=None, examples=[])]
