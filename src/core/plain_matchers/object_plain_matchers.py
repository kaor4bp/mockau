from typing import Annotated, Literal, Union

from pydantic import ConfigDict, Field

from core.plain_matchers.base_plain_matcher import (
    BaseAndPlainMatcher,
    BaseAnyPlainMatcher,
    BaseNotPlainMatcher,
    BaseOrPlainMatcher,
    BasePlainMatcher,
)
from core.plain_matchers.integer_plain_matchers import (
    IntegerAnd,
    IntegerAny,
    IntegerEqualTo,
    IntegerGreaterOrEqualThan,
    IntegerGreaterThan,
    IntegerLessOrEqualThan,
    IntegerLessThan,
    IntegerNot,
    IntegerOr,
)
from core.plain_matchers.string_plain_matchers import (
    StringAnd,
    StringAny,
    StringContains,
    StringEqualTo,
    StringNot,
    StringOr,
    StringPattern,
)


class BaseObjectPlainMatcher(BasePlainMatcher):
    pass


class ObjectPlainMatcher(BaseObjectPlainMatcher):
    model_config = ConfigDict(arbitrary_types_allowed=True)

    type_of: Literal['ObjectPlainMatcher'] = 'ObjectPlainMatcher'
    obj: dict
    obj_name: str | None = 'default'

    def is_subset_of(self, other):
        assert isinstance(other, BaseObjectPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            assert self.obj_name == other.obj_name

            banned_self_keys = []
            for other_key in other.obj.keys():
                is_success = False
                for self_key in self.obj.keys():
                    if self_key in banned_self_keys:
                        continue

                    if isinstance(other_key, str):
                        matcher_other_key = StringEqualTo(value=other_key)
                    else:
                        matcher_other_key = other_key
                    if isinstance(self_key, str):
                        matcher_self_key = StringEqualTo(value=self_key)
                    else:
                        matcher_self_key = self_key

                    if matcher_self_key.is_subset_of(matcher_other_key):
                        if self.obj[self_key].is_subset_of(other.obj[other_key]):
                            banned_self_keys.append(self_key)
                            is_success = True
                            break
                        else:
                            is_success = False

                if not is_success:
                    return False

            return True
        else:
            return other.is_subset_of(self)

    def is_intersected_with(self, other):
        assert isinstance(other, BaseObjectPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            assert self.obj_name == other.obj_name

            banned_other_keys = []
            for self_key in self.obj.keys():
                for other_key in other.obj.keys():
                    if other_key in banned_other_keys:
                        continue

                    if isinstance(self_key, str):
                        matcher_self_key = StringEqualTo(value=self_key)
                    else:
                        matcher_self_key = self_key
                    if isinstance(other_key, str):
                        matcher_other_key = StringEqualTo(value=other_key)
                    else:
                        matcher_other_key = other_key
                    if matcher_self_key.is_intersected_with(matcher_other_key):
                        if self.obj[self_key].is_intersected_with(other.obj[other_key]):
                            banned_other_keys.append(other_key)
                            break
                        else:
                            return False

            return True
        else:
            return other.is_intersected_with(self)


class ObjectAny(BaseObjectPlainMatcher, BaseAnyPlainMatcher):
    type_of: Literal['ObjectAny'] = 'ObjectAny'


class ObjectNot(BaseObjectPlainMatcher, BaseNotPlainMatcher['_t_ObjectPlainMatcher']):
    type_of: Literal['ObjectNot'] = 'ObjectNot'


class ObjectAnd(BaseObjectPlainMatcher, BaseAndPlainMatcher['_t_ObjectPlainMatcher']):
    type_of: Literal['ObjectAnd'] = 'ObjectAnd'


class ObjectOr(BaseObjectPlainMatcher, BaseOrPlainMatcher['_t_ObjectPlainMatcher']):
    type_of: Literal['ObjectOr'] = 'ObjectOr'


_t_ObjectPlainMatcher = Annotated[
    Union[
        ObjectPlainMatcher,
        ObjectAny,
        ObjectNot,
        ObjectAnd,
        ObjectOr,
    ],
    Field(discriminator='type_of'),
]

_t_PlainMatcher = Annotated[
    Union[
        IntegerEqualTo,
        IntegerGreaterThan,
        IntegerGreaterOrEqualThan,
        IntegerLessThan,
        IntegerLessOrEqualThan,
        IntegerAny,
        IntegerNot,
        IntegerAnd,
        IntegerOr,
        StringEqualTo,
        StringPattern,
        StringContains,
        StringAny,
        StringNot,
        StringAnd,
        StringOr,
        ObjectPlainMatcher,
        ObjectAny,
        ObjectNot,
        ObjectAnd,
        ObjectOr,
    ],
    Field(discriminator='type_of'),
]


ObjectPlainMatcher.model_rebuild()
ObjectAny.model_rebuild()
ObjectNot.model_rebuild()
ObjectAnd.model_rebuild()
ObjectOr.model_rebuild()
