from typing import Literal

import z3

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseNumberPredicate(BaseScalarPredicate):
    """Base class for number (real) predicates.

    .. Docstring created by Gemini 2.5 Flash
    """

    def get_all_predicates(self):
        yield self

    @property
    def predicate_types(self):
        """Get supported predicate types for this class.

        :return: Set containing only Real type
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return {PredicateType.Real}


class NumberEqualTo(BaseNumberPredicate):
    """Predicate for checking if a real number value is equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-minow-float-eq'] = '$-minow-float-eq'
    value: float

    def verify(self, value):
        return isinstance(value, float) and value == self.value

    def __invert__(self):
        return NumberNotEqualTo(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        """Convert the number equality predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the equality constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable == z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())


class NumberNotEqualTo(BaseNumberPredicate):
    type_of: Literal['$-minow-float-neq'] = '$-minow-float-neq'
    value: float

    def normalize_to_canonical_form(self):
        from core.predicates import OrPredicate

        return OrPredicate(
            predicates=[NumberGreaterThan(value=self.value), NumberLessThan(value=self.value)],
        ).normalize_to_canonical_form()

    def verify(self, value):
        return isinstance(value, float) and value != self.value

    def __invert__(self):
        return NumberEqualTo(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable != z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())


class NumberGreaterThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is greater than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-minow-float-gt'] = '$-minow-float-gt'
    value: float

    def verify(self, value):
        return isinstance(value, float) and value > self.value

    def __invert__(self):
        return NumberLessOrEqualThan(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        """Convert the number greater-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable > z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())


class NumberGreaterOrEqualThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is greater than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-minow-float-gte'] = '$-minow-float-gte'
    value: float

    def normalize_to_canonical_form(self):
        from core.predicates import OrPredicate

        return OrPredicate(
            predicates=[NumberGreaterThan(value=self.value), NumberEqualTo(value=self.value)],
        ).normalize_to_canonical_form()

    def verify(self, value):
        return isinstance(value, float) and value >= self.value

    def __invert__(self):
        return NumberLessThan(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        """Convert the number greater-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable >= z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())


class NumberLessThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is less than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-minow-float-lt'] = '$-minow-float-lt'
    value: float

    def verify(self, value):
        return isinstance(value, float) and value < self.value

    def __invert__(self):
        return NumberGreaterOrEqualThan(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        """Convert the number less-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable < z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())


class NumberLessOrEqualThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is less than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-minow-float-lte'] = '$-minow-float-lte'
    value: float

    def normalize_to_canonical_form(self):
        from core.predicates import OrPredicate

        return OrPredicate(
            predicates=[NumberLessThan(value=self.value), NumberEqualTo(value=self.value)],
        ).normalize_to_canonical_form()

    def verify(self, value):
        return isinstance(value, float) and value <= self.value

    def __invert__(self):
        return NumberGreaterThan(value=self.value, var=self.var)

    def to_z3(self, ctx: VariableContext):
        """Convert the number less-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        ctx.set_as_user_variable(self.var)
        return z3.And(real_variable <= z3.RealVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_real())
