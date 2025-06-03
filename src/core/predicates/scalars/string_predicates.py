from typing import Literal

import exrex
import z3
from z3 import InRe

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext
from utils.z3_helpers import ConvertEREToZ3Regex, string_to_case_insensitive_z3_regex

DEFAULT_REGEX_STRING_MAX_LENGTH = 20


def is_pattern_equal_to_string(value: str, pattern: str) -> bool:
    return all(value == generated_value for generated_value in exrex.generate(pattern))


class BaseStringPredicate(BaseScalarPredicate):
    @property
    def predicate_types(self):
        return {PredicateType.String}


class StringEqualTo(BaseStringPredicate):
    type_of: Literal['StringEqualTo'] = 'StringEqualTo'
    value: str
    ignore_case: bool = False

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        if self.ignore_case:
            z3_regex = ConvertEREToZ3Regex(self.value, is_case_sensitive=False).convert()
            expr = InRe(var, z3_regex)
        else:
            expr = var == self.value

        return expr


class StringPattern(BaseStringPredicate):
    type_of: Literal['StringPattern'] = 'StringPattern'
    pattern: str
    ignore_case: bool = False
    max_length: int = DEFAULT_REGEX_STRING_MAX_LENGTH

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        z3_regex = ConvertEREToZ3Regex(self.pattern, is_case_sensitive=not self.ignore_case).convert()
        expr = z3.And(z3.InRe(var, z3_regex), z3.Length(var) <= self.max_length)

        return expr


class StringContains(BaseStringPredicate):
    type_of: Literal['StringContains'] = 'StringContains'
    value: str
    ignore_case: bool = False
    max_length: int = DEFAULT_REGEX_STRING_MAX_LENGTH

    def to_z3(self, ctx: VariableContext):
        var = ctx.get_variable(self.predicate_type)
        any_char = z3.AllChar(z3.ReSort(z3.StringSort()))

        if self.ignore_case:
            expr = InRe(
                var,
                z3.simplify(
                    z3.Concat(
                        z3.Star(any_char),
                        string_to_case_insensitive_z3_regex(self.value),
                        z3.Star(any_char),
                    )
                ),
            )
        else:
            # expr = InRe(
            #     var,
            #     z3.Concat(
            #         z3.Star(any_char),
            #         z3.Re(z3.StringVal(self.value)),
            #         z3.Star(any_char),
            #     )
            # )
            expr = z3.Contains(var, self.value)

        expr = z3.And(expr, z3.Length(var) <= self.max_length)
        return expr
