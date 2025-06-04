from typing import Literal

from core.predicates.base_predicate import BaseScalarPredicate, PredicateType, VariableContext


class BaseBooleanPredicate(BaseScalarPredicate):
    """Base class for boolean predicates.

    .. Docstring created by Gemini 2.5 Flash
    """

    @property
    def predicate_types(self):
        """Get supported predicate types for this class.

        :return: Set containing only Boolean type
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return {PredicateType.Boolean}


class BooleanEqualTo(BaseBooleanPredicate):
    """Predicate for checking if a boolean value is equal to a specific value.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['BooleanEqualTo'] = 'BooleanEqualTo'
    value: bool

    def to_z3(self, ctx: VariableContext):
        """Convert the boolean equality predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the equality constraint.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        boolean_variable = ctx.get_variable(self.predicate_type)
        return boolean_variable == self.value
