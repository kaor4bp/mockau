from typing import Literal

import z3

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseNumberPredicate(BaseScalarPredicate):
    """Base class for number (real) predicates.

    .. Docstring created by Gemini 2.5 Flash
    """

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

    type_of: Literal['NumberEqualTo'] = 'NumberEqualTo'
    value: float

    def to_z3(self, ctx: VariableContext):
        """Convert the number equality predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the equality constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        return real_variable == z3.RealVal(self.value)


class NumberGreaterThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is greater than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NumberGreaterThan'] = 'NumberGreaterThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        """Convert the number greater-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        return real_variable > z3.RealVal(self.value)


class NumberGreaterOrEqualThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is greater than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NumberGreaterOrEqualThan'] = 'NumberGreaterOrEqualThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        """Convert the number greater-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        return real_variable >= z3.RealVal(self.value)


class NumberLessThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is less than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NumberLessThan'] = 'NumberLessThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        """Convert the number less-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        return real_variable < z3.RealVal(self.value)


class NumberLessOrEqualThan(BaseNumberPredicate):
    """Predicate for checking if a real number value is less than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NumberLessOrEqualThan'] = 'NumberLessOrEqualThan'
    value: float

    def to_z3(self, ctx: VariableContext):
        """Convert the number less-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        real_variable = ctx.get_variable(self.predicate_type)
        return real_variable <= z3.RealVal(self.value)
