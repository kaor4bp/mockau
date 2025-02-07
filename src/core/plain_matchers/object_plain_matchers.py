from core.plain_matchers.base_plain_matcher import BasePlainMatcher
from core.plain_matchers.common_plain_matchers import CommonPlainMatcher


class BaseObjectPlainMatcher(BasePlainMatcher):
    pass


class ObjectPlainMatcher(BaseObjectPlainMatcher):
    def __init__(self, obj: dict) -> None:
        self.obj: dict[str, 't_PlainMatcher'] = obj

    def is_subset(self, other):
        assert isinstance(other, BaseObjectPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            for key in other.obj.keys():
                if key not in self.obj.keys():
                    return False
                if not self.obj[key].is_subset(other.obj[key]):
                    return False
            return True
        else:
            return other.is_subset(self)

    def is_intersected(self, other):
        assert isinstance(other, BaseObjectPlainMatcher) or isinstance(other, CommonPlainMatcher)

        if isinstance(other, ObjectPlainMatcher):
            self_keys = set(self.obj.keys())
            other_keys = set(other.obj.keys())

            for key in self_keys.intersection(other_keys):
                if not self.obj[key].is_intersected(other.obj[key]):
                    return False
            return True
        else:
            return other.is_intersected(self)
