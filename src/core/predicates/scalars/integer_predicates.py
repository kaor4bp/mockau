from typing import Literal

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

    type_of: Literal['IntegerEqualTo'] = 'IntegerEqualTo'
    value: int

    def to_z3(self, ctx: VariableContext):
        """Convert the integer equality predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the equality constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return integer_variable == self.value


class IntegerGreaterThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is greater than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['IntegerGreaterThan'] = 'IntegerGreaterThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        """Convert the integer greater-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return integer_variable > self.value


class IntegerGreaterOrEqualThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is greater than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['IntegerGreaterOrEqualThan'] = 'IntegerGreaterOrEqualThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        """Convert the integer greater-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the greater-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return integer_variable >= self.value


class IntegerLessThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is less than a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['IntegerLessThan'] = 'IntegerLessThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        """Convert the integer less-than predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return integer_variable < self.value


class IntegerLessOrEqualThan(BaseIntegerPredicate):
    """Predicate for checking if an integer value is less than or equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['IntegerLessOrEqualThan'] = 'IntegerLessOrEqualThan'
    value: int

    def to_z3(self, ctx: VariableContext):
        """Convert the integer less-than-or-equal-to predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the less-than-or-equal-to constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        integer_variable = ctx.get_variable(self.predicate_type)
        return integer_variable <= self.value
