from functools import reduce
from typing import Any, Literal

import z3

from core.predicates.base_predicate import BaseLogicalPredicate, BaseScalarPredicate, PredicateType, VariableContext
from core.predicates.consts import PREDICATE_TYPE_TO_PYTHON_TYPE
from core.predicates.context.variable_context import PredicateLimitations


class VoidPredicate(BaseLogicalPredicate):
    type_of: Literal['VoidPredicate'] = 'VoidPredicate'

    def verify(self, value):
        raise ValueError("VoidPredicate cannot be used for verification -- it is impossible value")

    @property
    def predicate_types(self):
        return {PredicateType.Undefined}

    def to_z3(self, ctx: VariableContext):
        return z3.BoolVal(False, ctx=ctx.z3_context)

    def __invert__(self):
        return AnyPredicate()


class AnyPredicate(BaseScalarPredicate):
    """Predicate that matches any value and any type.

    Always returns True for `is_matched` and is represented by a Z3 BoolVal(True).

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['AnyPredicate'] = 'AnyPredicate'

    def verify(self, value):
        return True

    def __invert__(self):
        return VoidPredicate()

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
        return z3.BoolVal(True, ctx=ctx.z3_context)


class NotPredicate(BaseLogicalPredicate):
    """Predicate representing the logical NOT operation on another predicate.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['NotPredicate'] = 'NotPredicate'
    predicate: Any
    preserve_type: bool = True

    def __invert__(self):
        return self.predicate

    def verify(self, value):
        all_types = {
            PredicateType.Null,
            PredicateType.Boolean,
            PredicateType.Integer,
            PredicateType.Real,
            PredicateType.String,
            PredicateType.Object,
            PredicateType.Array,
        }
        other_types = all_types - self.predicate_types

        constraints = [not self.predicate.verify(value)]
        if not self.preserve_type:
            for other_type in other_types:
                constraints.append(isinstance(value, PREDICATE_TYPE_TO_PYTHON_TYPE[other_type]))
        return any(constraints)

    @property
    def predicate_types(self) -> set[PredicateType]:
        return self.predicate.predicate_types

    def calculate_limitations(self) -> PredicateLimitations:
        return (~self.predicate).calculate_limitations()

    def to_z3(self, ctx: VariableContext):
        inverted_predicate = ~self.predicate
        additional_constraints = []

        if self.preserve_type is False and PredicateType.Any not in self.predicate_types:
            all_types = {
                PredicateType.Null,
                PredicateType.Boolean,
                PredicateType.Integer,
                PredicateType.Real,
                PredicateType.String,
                PredicateType.Object,
                PredicateType.Array,
            }
            other_types = all_types - self.predicate_types

            for other_type in other_types:
                ctx.get_variable(other_type)

                if other_type == PredicateType.Null:
                    additional_constraints.append(ctx.json_type_variable.is_null())
                elif other_type == PredicateType.Boolean:
                    additional_constraints.append(ctx.json_type_variable.is_bool())
                elif other_type == PredicateType.Integer:
                    additional_constraints.append(ctx.json_type_variable.is_int())
                elif other_type == PredicateType.Real:
                    additional_constraints.append(ctx.json_type_variable.is_real())
                elif other_type == PredicateType.String:
                    additional_constraints.append(ctx.json_type_variable.is_str())
                elif other_type == PredicateType.Object:
                    additional_constraints.append(ctx.json_type_variable.is_object())
                elif other_type == PredicateType.Array:
                    additional_constraints.append(ctx.json_type_variable.is_array())
                else:
                    raise ValueError(f"Unknown predicate type: {other_type}")
        return z3.Or(inverted_predicate.to_z3(ctx), *additional_constraints)


class AndPredicate(BaseLogicalPredicate):
    """Predicate representing the logical AND operation on a list of predicates.

    The `predicate_types` property returns the intersection of all inner predicate types.
    If the intersection is empty, it means no common type can satisfy all predicates,
    so it returns {PredicateType.Null}.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['AndPredicate'] = 'AndPredicate'
    predicates: list

    def verify(self, value):
        return all(p.verify(value) for p in self.predicates)

    def calculate_limitations(self) -> PredicateLimitations:
        if self.predicates:
            return PredicateLimitations()
        else:
            limitation = self.predicates[0].calculate_limitations()
            for other_limitation in self.predicates[1:]:
                limitation.push(other_limitation)
            return limitation

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

    def __invert__(self):
        return OrPredicate(predicates=[NotPredicate(predicate=p) for p in self.predicates])

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
            return z3.BoolVal(False, ctx=ctx.z3_context)
        else:
            return z3.And(
                [inner_predicate.to_z3(ctx) for inner_predicate in self.predicates]
                + [z3.BoolVal(True, ctx=ctx.z3_context)]
            )


class OrPredicate(BaseLogicalPredicate):
    """Predicate representing the logical OR operation on a list of predicates.

    The `predicate_types` property returns the union of all inner predicate types.

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['OrPredicate'] = 'OrPredicate'
    predicates: list

    def verify(self, value):
        return any(p.verify(value) for p in self.predicates)

    @property
    def predicate_types(self) -> set[PredicateType]:
        """Get supported predicate types for this class.

        Returns the union of all inner predicate types.

        :return: Set of all supported types from the inner predicates.
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        return set.union(*[inner_predicate.predicate_types for inner_predicate in self.predicates])

    def __invert__(self):
        return AndPredicate(predicates=[NotPredicate(predicate=p) for p in self.predicates])

    def calculate_limitations(self) -> PredicateLimitations:
        if self.predicates:
            return PredicateLimitations()
        else:
            limitation = self.predicates[0].calculate_limitations()
            for other_limitation in self.predicates[1:]:
                limitation.push(other_limitation)
            return limitation

    def to_z3(self, ctx: VariableContext):
        """Convert the OR predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the logical OR of all inner predicates.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        or_predicates = [z3.BoolVal(False, ctx=ctx.z3_context)]
        or_predicates += [inner_predicate.to_z3(ctx) for inner_predicate in self.predicates]

        return z3.Or(*or_predicates)
