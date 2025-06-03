from abc import ABC, abstractmethod
from enum import Enum
from uuid import UUID, uuid4

import z3
from pydantic import Field
from typing_extensions import TypeVar

from core.bases.base_schema import BaseSchema

t_Predicate = TypeVar('t_Predicate', bound='BasePredicate')


class PredicateType(Enum):
    Boolean = 'Boolean'
    Integer = 'Integer'
    Real = 'Real'
    String = 'String'

    Object = 'Object'
    Array = 'Array'

    Null = 'Null'
    Any = 'Any'


class VariableContext:
    _JSON_TYPES = {}
    MAX_NESTING_LEVEL = 100

    @classmethod
    def _build_json_type(cls, level: int = -1):
        if cls._JSON_TYPES.get(level):
            return cls._JSON_TYPES[level]

        JsonType = z3.Datatype(f'JsonType_{level}')

        JsonType.declare('int', ('get_int', z3.IntSort()))
        JsonType.declare('bool', ('get_bool', z3.BoolSort()))
        JsonType.declare('str', ('get_str', z3.StringSort()))
        JsonType.declare('real', ('get_real', z3.RealSort()))

        if level > 0:
            NestedJsonType = cls._build_json_type(level - 1)
            NestedJsonArraySort = z3.ArraySort(z3.StringSort(), NestedJsonType)
            JsonType.declare(
                'object',
                ('get_object', NestedJsonArraySort),
                ('get_object_keys_quantity', z3.IntSort()),
                ('get_object_keys', z3.SetSort(z3.StringSort())),
            )

        JsonType = JsonType.create()
        cls._JSON_TYPES[level] = JsonType
        return JsonType

    def __init__(self, level: int | None = None) -> None:
        if not self._JSON_TYPES:
            self._build_json_type(level=self.MAX_NESTING_LEVEL)
        if not level:
            level = max(self._JSON_TYPES.keys())
        self._level = level

        self._var_id = uuid4()
        self._var = z3.Const(f'json_var_{self._var_id}', self.JsonType)

        self._children = []
        self._var_type_constraints = {}
        self._global_constraints = []

    @property
    def JsonType(self):
        return self._JSON_TYPES[self._level]

    @property
    def json_type_variable(self):
        return self._var

    def create_child_context(self) -> 'VariableContext':
        child_context = VariableContext(level=self._level - 1)
        self._children.append(child_context)
        return child_context

    def push_to_global_constraints(self, expr) -> None:
        self._global_constraints.append(expr)

    def _allow_var_type_for_variable(self, predicate_type: PredicateType) -> None:
        if predicate_type not in self._var_type_constraints.keys():
            self._var_type_constraints[predicate_type] = self._generate_type_expression(predicate_type)

    def get_variable(self, predicate_type: PredicateType):
        self._allow_var_type_for_variable(predicate_type)

        if predicate_type is PredicateType.String:
            return self.JsonType.get_str(self._var)
        elif predicate_type is PredicateType.Integer:
            return self.JsonType.get_int(self._var)
        elif predicate_type is PredicateType.Real:
            return self.JsonType.get_real(self._var)
        elif predicate_type is PredicateType.Boolean:
            return self.JsonType.get_bool(self._var)
        elif predicate_type is PredicateType.Object:
            return self.JsonType.get_object(self._var)
        else:
            raise NotImplementedError(f'get_variable for predicate type {predicate_type} not implemented yet')

    def _generate_type_expression(
        self,
        predicate_type: PredicateType,
    ) -> z3.BoolRef:
        type_expressions = {
            PredicateType.String: self.JsonType.is_str(self._var),
            PredicateType.Integer: self.JsonType.is_int(self._var),
            PredicateType.Real: self.JsonType.is_real(self._var),
            PredicateType.Boolean: self.JsonType.is_bool(self._var),
            PredicateType.Object: self.JsonType.is_object(self._var),
        }

        type_expr = z3.And(
            [
                type_expr if type_pt == predicate_type else z3.Not(type_expr)
                for type_pt, type_expr in type_expressions.items()
            ]
        )
        return type_expr

    def to_global_constraints(self) -> z3.BoolRef:
        type_expressions = list(self._var_type_constraints.values())
        type_one_of_expr = type_expressions.pop(0)
        for type_expr in type_expressions:
            type_one_of_expr = z3.Xor(type_one_of_expr, type_expr)
        type_one_of_expr = z3.simplify(type_one_of_expr)

        child_constraints = [child.to_global_constraints() for child in self._children]
        return z3.simplify(
            z3.And(
                type_one_of_expr,
                *self._global_constraints,
                *child_constraints,
            )
        )


class BasePredicate(BaseSchema, ABC):
    internal_id: UUID = Field(default_factory=uuid4, exclude=True)

    def __hash__(self):
        return hash(self.internal_id)

    @abstractmethod
    def to_z3(self, var: VariableContext) -> z3.ExprRef: ...

    @property
    @abstractmethod
    def predicate_types(self) -> set[PredicateType]: ...

    def is_subset_of(self, other: t_Predicate) -> bool:
        solver = z3.Solver()
        solver.set("timeout", 100000)

        ctx = VariableContext()
        solver.add(z3.And(self.to_z3(ctx), z3.Not(other.to_z3(ctx))))
        solver.add(ctx.to_global_constraints())

        result = solver.check()
        # solver.model().eval(ctx.get_variable(PredicateType.Object)[z3.StringVal('lol')], model_completion=True)
        assert result != z3.unknown
        return result in [z3.unsat, z3.unknown]

    def is_superset_of(self, other: t_Predicate) -> bool:
        solver = z3.Solver()
        ctx = VariableContext()
        solver.set("timeout", 100000)

        solver.add(other.to_z3(ctx))
        solver.add(z3.Not(self.to_z3(ctx)))
        solver.add(ctx.to_global_constraints())

        result = solver.check()
        assert result != z3.unknown
        return result in [z3.unsat, z3.unknown]

    def is_intersected_with(self, other: t_Predicate) -> bool:
        solver = z3.Solver()
        ctx = VariableContext()
        solver.set("timeout", 100000)

        solver.add(other.to_z3(ctx))
        solver.add(self.to_z3(ctx))
        solver.add(ctx.to_global_constraints())

        result = solver.check()
        assert result != z3.unknown
        return result == z3.sat

    def is_matched(self, value) -> bool:
        for pt in self.predicate_types:
            solver = z3.Solver()
            ctx = VariableContext()
            var = ctx.get_variable(pt)
            solver.add(self.to_z3(ctx))
            solver.add(var == value)
            solver.add(ctx.to_global_constraints())
            if solver.check() == z3.sat:
                return True
        else:
            return False

    def is_equivalent_to(self, other):
        return self.is_subset_of(other) and self.is_superset_of(other)


class BaseScalarPredicate(BasePredicate, ABC):
    @property
    def predicate_type(self) -> PredicateType:
        return list(self.predicate_types)[0]


class BaseCollectionPredicate(BasePredicate, ABC):
    pass


class BaseLogicalPredicate(BaseScalarPredicate, ABC):
    pass
