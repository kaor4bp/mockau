from functools import reduce
from typing import Any, Literal

import z3

from core.predicates.base_predicate import BaseLogicalPredicate, BaseScalarPredicate, PredicateType, VariableContext


class AnyPredicate(BaseScalarPredicate):
    """Predicate that matches any value and any type.

    Always returns True for `is_matched` and is represented by a Z3 BoolVal(True).

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['AnyPredicate'] = 'AnyPredicate'

    @property
    def predicate_types(self):
        """Get supported predicate types for this class.

        :return: Set containing only Any type
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return {PredicateType.Any}

    def to_z3(self, ctx: VariableContext):
        """Convert the any predicate to a Z3 expression.

        This predicate always returns a Z3 Boolean True value.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 Boolean True value.
        :rtype: z3.BoolRef

        .. Docstring created by Gemini 2.5 Flash
        """
        return z3.BoolVal(True)


class NotPredicate(BaseLogicalPredicate):
    """Predicate representing the logical NOT operation on another predicate.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NotPredicate'] = 'NotPredicate'
    predicate: Any

    @property
    def predicate_types(self) -> set[PredicateType]:
        """Get supported predicate types for this class.

        The predicate types are inherited from the inner predicate.

        :return: Set of supported types from the inner predicate.
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return self.predicate.predicate_types

    def to_z3(self, ctx: VariableContext):
        """Convert the NOT predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the logical NOT of the inner predicate.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        return z3.Not(self.predicate.to_z3(ctx))


class AndPredicate(BaseLogicalPredicate):
    """Predicate representing the logical AND operation on a list of predicates.

    The `predicate_types` property returns the intersection of all inner predicate types.
    If the intersection is empty, it means no common type can satisfy all predicates,
    so it returns {PredicateType.Null}.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['AndPredicate'] = 'AndPredicate'
    predicates: list

    @property
    def predicate_types(self) -> set[PredicateType]:
        """Get supported predicate types for this class.

        Returns the intersection of all inner predicate types. If no common types exist,
        it returns a set containing only `PredicateType.Null`.

        :return: Set of common supported types, or {PredicateType.Null}.
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        intersected_types = reduce(lambda x, y: x & y, [p.predicate_types for p in self.predicates])
        if intersected_types:
            return intersected_types
        else:
            return {PredicateType.Null}

    def to_z3(self, ctx: VariableContext):
        """Convert the AND predicate to a Z3 expression.

        If the common predicate types result in Null, it returns a Z3 Boolean False.
        Otherwise, it returns a Z3 expression representing the logical AND of all inner predicates.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the logical AND.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        if self.predicate_types == {PredicateType.Null}:
            return z3.BoolVal(False)
        else:
            return z3.And([inner_predicate.to_z3(ctx) for inner_predicate in self.predicates])


class OrPredicate(BaseLogicalPredicate):
    """Predicate representing the logical OR operation on a list of predicates.

    The `predicate_types` property returns the union of all inner predicate types.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['OrPredicate'] = 'OrPredicate'
    predicates: list

    @property
    def predicate_types(self) -> set[PredicateType]:
        """Get supported predicate types for this class.

        Returns the union of all inner predicate types.

        :return: Set of all supported types from the inner predicates.
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return set.union(*[inner_predicate.predicate_types for inner_predicate in self.predicates])

    def to_z3(self, ctx: VariableContext):
        """Convert the OR predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the logical OR of all inner predicates.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        return z3.Or([inner_predicate.to_z3(ctx) for inner_predicate in self.predicates])
