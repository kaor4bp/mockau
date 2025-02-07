from typing import Annotated, Literal, Union

from pydantic import Field

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
    type_of: Literal['ObjectPlainMatcher'] = 'ObjectPlainMatcher'
    obj: dict[str, '_t_PlainMatcher']
    obj_name: str

    def is_subset(self, other):
        assert isinstance(other, BaseObjectPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            assert self.obj_name == other.obj_name

            for key in other.obj.keys():
                if key not in self.obj.keys():
                    return False
                if not self.obj[key].is_subset(other.obj[key]):
                    return False
            return True
        else:
            return other.is_subset(self)

    def is_intersected(self, other):
        assert isinstance(other, BaseObjectPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            assert self.obj_name == other.obj_name

            self_keys = set(self.obj.keys())
            other_keys = set(other.obj.keys())

            for key in self_keys.intersection(other_keys):
                if not self.obj[key].is_intersected(other.obj[key]):
                    return False
            return True
        else:
            return other.is_intersected(self)


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
