from functools import cached_property, reduce
from typing import TYPE_CHECKING, Literal, TypeVar

import z3

from core.predicates.base_predicate import (
    BaseLogicalPredicate,
    BaseScalarPredicate,
    ParityPredicateMixin,
    PredicateType,
    VariableContext,
)
from core.predicates.consts import ALLOWED_POOL_PREDICATE_TYPES, PREDICATE_TYPE_TO_PYTHON_TYPE
from core.predicates.context.predicate_limitations import PredicateLimitations
from core.predicates.helpers import py_value_to_predicate

if TYPE_CHECKING:
    from core.predicates import t_DefaultPredicateType

_t_SpecifiedType = TypeVar('_t_SpecifiedType')


class VoidPredicate(BaseLogicalPredicate):
    type_of: Literal['$-mockau-void'] = '$-mockau-void'

    def verify(self, value):
        return False
        # raise ValueError("VoidPredicate cannot be used for verification -- it is impossible value")

    @property
    def predicate_types(self):
        return {PredicateType.Any}

    def to_z3(self, ctx: VariableContext):
        return z3.BoolVal(False, ctx=ctx.z3_context)

    def __invert__(self):
        return AnyPredicate()


class AnyPredicate(BaseScalarPredicate):
    """Predicate that matches any value and any type.

    Always returns True for `is_matched` and is represented by a Z3 BoolVal(True).

    .. Docstring created by Gemini 2.5 Flash
    """

    type_of: Literal['$-mockau-any'] = '$-mockau-any'

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


class NotPredicate(BaseLogicalPredicate, ParityPredicateMixin):
    type_of: Literal['$-mockau-not'] = '$-mockau-not'

    predicate: 't_DefaultPredicateType'

    def normalize_to_canonical_form(self):
        value = self.compiled_value.normalize_to_canonical_form()

        if isinstance(value, VoidPredicate):
            return AnyPredicate()
        if isinstance(value, AnyPredicate):
            return VoidPredicate()

        if isinstance(value, NotPredicate):
            return (~value).normalize_to_canonical_form()
        else:
            return NotPredicate(predicate=value.normalize_to_canonical_form())

    @cached_property
    def compiled_value(self):
        p = py_value_to_predicate(self.predicate)
        if isinstance(p, ParityPredicateMixin):
            p._parity = not self._parity
        return p

    def __invert__(self):
        return self.compiled_value

    def verify(self, value):
        # Special handling for double negation: NOT(NOT(P)) should behave like P
        if self._parity and isinstance(self.compiled_value, NotPredicate) and not self.compiled_value._parity:
            # This is double negation NOT(NOT(P)), delegate to the inner predicate P
            return self.compiled_value.compiled_value.verify(value)

        other_types = ALLOWED_POOL_PREDICATE_TYPES - self.predicate_types

        constraints = [not self.compiled_value.verify(value)]
        for other_type in other_types:
            constraints.append(isinstance(value, PREDICATE_TYPE_TO_PYTHON_TYPE[other_type]))
        return any(constraints)

    @property
    def predicate_types(self) -> set[PredicateType]:
        if self._parity:
            if isinstance(self.compiled_value, NotPredicate):
                return self.compiled_value.compiled_value.predicate_types
            else:
                return self.compiled_value.predicate_types
        else:
            return ALLOWED_POOL_PREDICATE_TYPES

    def calculate_limitations(self) -> PredicateLimitations:
        return (~self.compiled_value).calculate_limitations()

    def to_z3(self, ctx: VariableContext):
        inverted_predicate = ~self.compiled_value
        additional_constraints = []

        if PredicateType.Any not in self.predicate_types:
            other_types = ALLOWED_POOL_PREDICATE_TYPES - self.predicate_types

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


class AndPredicate(BaseLogicalPredicate, ParityPredicateMixin):
    type_of: Literal['$-mockau-and'] = '$-mockau-and'

    predicates: list['t_DefaultPredicateType']

    def normalize_to_canonical_form(self):
        """
        Normalizes the predicate by transforming it into Conjunctive Normal Form (CNF)
        using De Morgan's laws: ``AND(P1, P2, ...)`` becomes ``NOT(OR(NOT(P1), NOT(P2), ...))``.

        This specific normalization strategy is intentionally applied to ensure that
        logically equivalent ``AND`` predicates result in identical normalized forms.
        The primary goal of this normalization is to facilitate the robust
        verification of predicate equivalence, allowing for direct comparison
        after transformation to a canonical CNF representation.

        :returns: A new ``NotPredicate`` instance representing the CNF form.
        :rtype: NotPredicate

        .. Generated by Athena (Gemini 2.5 Flash).
        """

        flattened_predicates = []
        for p in self.compiled_value:
            if isinstance(p, AndPredicate):
                flattened_predicates += p.compiled_value
            else:
                flattened_predicates.append(p)

        unique_flattened_predicates = {}
        for p in flattened_predicates:
            if isinstance(p, AnyPredicate):
                continue
            unique_flattened_predicates[p.model_dump_json(by_alias=True)] = p
        flattened_predicates = list(unique_flattened_predicates.values())

        if any(isinstance(p, VoidPredicate) for p in flattened_predicates):
            return VoidPredicate()

        if len(flattened_predicates) == 1:
            return flattened_predicates[0].normalize_to_canonical_form()
        if len(flattened_predicates) == 0:
            return VoidPredicate()

        flattened_predicates.sort(key=lambda x: x.model_dump_json(by_alias=True))

        return NotPredicate(
            predicate=OrPredicate(
                predicates=[NotPredicate(predicate=p) for p in flattened_predicates]
            ).normalize_to_canonical_form()
        ).normalize_to_canonical_form()

    @cached_property
    def compiled_value(self):
        assert isinstance(self.predicates, list)

        items = [py_value_to_predicate(item) for item in self.predicates]
        for item in items:
            if isinstance(item, ParityPredicateMixin):
                item._parity = self._parity

        return items

    def verify(self, value):
        return all(p.verify(value) for p in self.compiled_value)

    def calculate_limitations(self) -> PredicateLimitations:
        if not self.predicates:
            return PredicateLimitations()
        else:
            limitation = self.compiled_value[0].calculate_limitations()
            for other_limitation in self.compiled_value[1:]:
                limitation.push(other_limitation.calculate_limitations())
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
        intersected_types = reduce(lambda x, y: x & y, [p.predicate_types for p in self.compiled_value])
        if intersected_types:
            return intersected_types
        else:
            return {PredicateType.Null}

    def __invert__(self):
        return OrPredicate(predicates=[~p for p in self.compiled_value])

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
            z3_constraints = [inner_predicate.to_z3(ctx) for inner_predicate in self.compiled_value]
            if len(z3_constraints) == 0:
                return z3.BoolVal(True, ctx=ctx.z3_context)
            elif len(z3_constraints) == 1:
                return z3_constraints[0]
            else:
                return z3.And(*z3_constraints)


class OrPredicate(BaseLogicalPredicate, ParityPredicateMixin):
    type_of: Literal['$-mockau-or'] = '$-mockau-or'

    predicates: list['t_DefaultPredicateType']

    def normalize_to_canonical_form(self):
        flattened_predicates = []
        for p in self.compiled_value:
            if isinstance(p, OrPredicate):
                flattened_predicates += [sub_p.normalize_to_canonical_form() for sub_p in p.compiled_value]
            else:
                flattened_predicates.append(p.normalize_to_canonical_form())

        unique_flattened_predicates = {}
        for p in flattened_predicates:
            if isinstance(p, VoidPredicate):
                continue
            unique_flattened_predicates[p.model_dump_json(by_alias=True)] = p
        flattened_predicates = list(unique_flattened_predicates.values())

        if any(isinstance(p, AnyPredicate) for p in flattened_predicates):
            return AnyPredicate()

        if len(flattened_predicates) == 1:
            return flattened_predicates[0]
        if len(flattened_predicates) == 0:
            return AnyPredicate()

        flattened_predicates.sort(key=lambda x: x.model_dump_json(by_alias=True))

        return OrPredicate(predicates=flattened_predicates)

    @cached_property
    def compiled_value(self):
        assert isinstance(self.predicates, list)
        items = [py_value_to_predicate(item) for item in self.predicates]
        for item in items:
            if isinstance(item, ParityPredicateMixin):
                item._parity = self._parity

        return items

    def verify(self, value):
        return any(p.verify(value) for p in self.compiled_value)

    @property
    def predicate_types(self) -> set[PredicateType]:
        """Get supported predicate types for this class.

        Returns the union of all inner predicate types.

        :return: Set of all supported types from the inner predicates.
        :rtype: set[PredicateType]

        .. Docstring created by Gemini 2.5 Flash
        """
        if self.predicates:
            return set.union(*[inner_predicate.predicate_types for inner_predicate in self.compiled_value])
        else:
            return set()

    def __invert__(self):
        return AndPredicate(predicates=[~(p) for p in self.compiled_value])

    def calculate_limitations(self) -> PredicateLimitations:
        if not self.predicates:
            return PredicateLimitations()
        else:
            limitation = self.compiled_value[0].calculate_limitations()
            for other_limitation in self.compiled_value[1:]:
                limitation.push(other_limitation.calculate_limitations())
            return limitation

    def to_z3(self, ctx: VariableContext):
        """Convert the OR predicate to a Z3 expression.

        :param ctx: The variable context for Z3 expressions.
        :type ctx: VariableContext
        :return: A Z3 expression representing the logical OR of all inner predicates.
        :rtype: z3.ExprRef

        .. Docstring created by Gemini 2.5 Flash
        """
        z3_constraints = [inner_predicate.to_z3(ctx) for inner_predicate in self.compiled_value]
        if len(z3_constraints) == 0:
            return z3.BoolVal(False, ctx=ctx.z3_context)
        elif len(z3_constraints) == 1:
            return z3_constraints[0]
        else:
            return z3.Or(*z3_constraints)
