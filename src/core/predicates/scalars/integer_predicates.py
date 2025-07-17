from typing import Literal

import z3

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseIntegerPredicate(BaseScalarPredicate):
    """Base class for integer predicates.

    .. Docstring created by Gemini 2.5 Flash
    """

    @property
    def predicate_types(self):
        """Get supported predicate types for this class.

        :return: Set containing only Integer type
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return {PredicateType.Integer}


class IntegerEqualTo(BaseIntegerPredicate):
    """Predicate for checking if an integer value is equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-integer-eq'] = '$-mockau-integer-eq'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value == self.value

    def __invert__(self):
        return IntegerNotEqualTo(value=self.value)

    def to_z3(self, ctx: VariableContext):
        """Convert the integer equality predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the equality constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable == z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())


class IntegerNotEqualTo(BaseIntegerPredicate):
    type_of: Literal['$-mockau-integer-neq'] = '$-mockau-integer-neq'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value != self.value

    def __invert__(self):
        return IntegerEqualTo(value=self.value)

    def to_z3(self, ctx: VariableContext):
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable != z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())


class IntegerGreaterThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is greater than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-integer-gt'] = '$-mockau-integer-gt'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value > self.value

    def __invert__(self):
        return IntegerLessOrEqualThan(value=self.value)

    def to_z3(self, ctx: VariableContext):
        """Convert the integer greater-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable > z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())


class IntegerGreaterOrEqualThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is greater than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-integer-gte'] = '$-mockau-integer-gte'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value >= self.value

    def __invert__(self):
        return IntegerLessThan(value=self.value)

    def to_z3(self, ctx: VariableContext):
        """Convert the integer greater-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable >= z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())


class IntegerLessThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is less than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-integer-lt'] = '$-mockau-integer-lt'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value < self.value

    def __invert__(self):
        return IntegerGreaterOrEqualThan(value=self.value)

    def to_z3(self, ctx: VariableContext):
        """Convert the integer less-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable < z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())


class IntegerLessOrEqualThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is less than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-integer-lte'] = '$-mockau-integer-lte'
    value: int

    def verify(self, value):
        return isinstance(value, int) and value <= self.value

    def __invert__(self):
        return IntegerGreaterThan(value=self.value)

    def to_z3(self, ctx: VariableContext):
        """Convert the integer less-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return z3.And(integer_variable <= z3.IntVal(self.value, ctx=ctx.z3_context), ctx.json_type_variable.is_int())
