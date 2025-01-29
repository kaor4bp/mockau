from schemas.common_matchers.abstract_matcher import AbstractMatcher

# class IntegerGreatOrEqualMatcher(AbstractMatcher):
#     gte: int
#
#     def is_matched(self, value: int) -> bool:
#         return value >= self.gte
#
#
# class IntegerGreatMatcher(AbstractMatcher):
#     gt: int
#
#     def is_matched(self, value: int) -> bool:
#         return value > self.gt
#
#
# class IntegerLessOrEqualMatcher(AbstractMatcher):
#     lte: int
#
#     def is_matched(self, value: int) -> bool:
#         return value <= self.lte
#
#
# class IntegerLessMatcher(AbstractMatcher):
#     lt: int
#
#     def is_matched(self, value: int) -> bool:
#         return value < self.lt
#
#
# class IntegerEqualToMatcher(AbstractMatcher):
#     equal_to: int
#
#     def is_matched(self, value: int) -> bool:
#         return value == self.equal_to
#
#
# class IntegerMultiplyOfMatcher(AbstractMatcher):
#     multiply_of: int
#
#     def is_matched(self, value: int) -> bool:
#         return value % self.multiply_of == 0
#
#
# class IntegerAndMatcher(AndMatcher['t_IntegerMatcher']):
#     and_: list['t_IntegerMatcher'] = Field(examples=[
#         [{'equal_to': 6}, {'multiply_of': 2}],
#         [{'lt': 7}],
#     ])
#
#
# class IntegerOrMatcher(OrMatcher['t_IntegerMatcher']):
#     or_: list['t_IntegerMatcher'] = Field(examples=[
#         [{'equal_to': 5}, {'equal_to': 6}],
#         [{'gte': 8}],
#     ])
#
#
# class IntegerNotMatcher(NotMatcher['t_IntegerMatcher']):
#     not_: 't_IntegerMatcher' = Field(examples=[
#         {'equal_to': 5},
#         {'multiply_of': 7},
#         {'gte': 8},
#     ])
#
#
# t_IntegerMatcher = Union[
#     IntegerGreatOrEqualMatcher,
#     IntegerGreatMatcher,
#     IntegerLessOrEqualMatcher,
#     IntegerLessMatcher,
#     IntegerEqualToMatcher,
#     IntegerMultiplyOfMatcher,
#     IntegerAndMatcher,
#     IntegerOrMatcher,
#     IntegerNotMatcher,
# ]


class IntegerMatcher(AbstractMatcher):
    equal_to: int | None = None
    gte: int | None = None
    gt: int | None = None
    lte: int | None = None
    lt: int | None = None
    multiply_of: int | None = None

    and_: list['IntegerMatcher'] | None = None
    or_: list['IntegerMatcher'] | None = None
    not_: 'IntegerMatcher | None' = None

    def is_matched(self, value: int) -> bool:
        if self.equal_to is not None and self.equal_to != value:
            return False
        if self.gte is not None and value < self.gte:
            return False
        if self.gt is not None and value <= self.gt:
            return False
        if self.lte is not None and value > self.lte:
            return False
        if self.lt is not None and value >= self.lt:
            return False
        if self.multiply_of is not None and value % self.multiply_of != 0:
            return False
        if self.and_ and any(not item.is_matched(value) for item in self.and_):
            return False
        if self.or_ and all(not item.is_matched(value) for item in self.or_):
            return False
        if self.not_ and self.not_.is_matched(value):
            return False
        return True


t_IntegerMatcher = IntegerMatcher
