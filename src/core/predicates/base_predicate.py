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


class ObjectContext:
    def __init__(self) -> None:
        self.variables = {}
        self._object_id = uuid4()

        self.key_variables = []
        self.value_variables = []
        self.type_variables = []
        self.all_keys_variable = z3.Const(f'obj_{self._object_id}_set_all_keys', z3.SetSort(z3.StringSort()))
        self.all_keys_quantity_variable = z3.Const(f'obj_{self._object_id}_set_all_keys_quantity', z3.IntSort())

    def get_key_context(self, index: int):
        if len(self.key_variables) <= index:
            self.key_variables.append(VariableContext())
            return self.get_key_context(index)
        return self.key_variables[index]

    def get_value_context(self, index: int):
        if len(self.value_variables) <= index:
            self.value_variables.append(VariableContext())
            return self.get_value_context(index)
        return self.value_variables[index]

    def get_type_sequence_var(self, index: int):
        if len(self.type_variables) <= index:
            self.type_variables.append(z3.Const(f'obj_{self._object_id}_type_seq_{index}', z3.SetSort(z3.StringSort())))
            return self.get_type_sequence_var(index)
        return self.type_variables[index]


class VariableContext:
    def __init__(self) -> None:
        self._variables = {}
        self._var_id = uuid4()

    def _get_z3_var(self, predicate_type: PredicateType) -> z3.ExprRef:
        match predicate_type:
            case PredicateType.Boolean:
                return z3.Bool(f'bool_{self._var_id}')
            case PredicateType.Integer:
                return z3.Int(f'int_{self._var_id}')
            case PredicateType.Real:
                return z3.Real(f'real_{self._var_id}')
            case PredicateType.String:
                return z3.String(f'str_{self._var_id}')
            case PredicateType.Object:
                return ObjectContext()
            case _:
                raise NotImplementedError(f'Lol - {predicate_type.value} is not supported yet. ')

    def get_variable(self, predicate_type: PredicateType):
        if predicate_type not in self._variables.keys():
            self._variables[predicate_type] = self._get_z3_var(predicate_type)
        return self._variables[predicate_type]


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
        if len(self.predicate_types) > len(other.predicate_types):
            return False

        solver = z3.Solver()
        solver.set("timeout", 1000)

        for pt in self.predicate_types:
            if pt == PredicateType.Null:
                continue
            if pt == PredicateType.Any:
                return True
            if pt not in other.predicate_types:
                continue

            solver.reset()
            ctx = VariableContext()
            solver.add(z3.Not(other.to_z3(ctx)))
            solver.add(self.to_z3(ctx))

            result = solver.check()
            # assert result != z3.unknown
            if result in [z3.unsat, z3.unknown]:
                return True
        else:
            return False

    def is_superset_of(self, other: t_Predicate) -> bool:
        if len(self.predicate_types) < len(other.predicate_types):
            return False

        solver = z3.Solver()
        ctx = VariableContext()
        solver.set("timeout", 1000)

        for pt in self.predicate_types:
            if pt == PredicateType.Null:
                continue
            if pt == PredicateType.Any:
                return True
            if pt not in other.predicate_types:
                continue

            solver.reset()
            solver.add(other.to_z3(ctx))
            solver.add(z3.Not(self.to_z3(ctx)))

            result = solver.check()
            # assert result != z3.unknown
            if result in [z3.unsat, z3.unknown]:
                return True
        else:
            return False

    def is_intersected_with(self, other: t_Predicate) -> bool:
        solver = z3.Solver()
        ctx = VariableContext()
        solver.set("timeout", 1000)

        for pt in self.predicate_types:
            if pt == PredicateType.Null:
                continue
            if pt == PredicateType.Any:
                return True
            if pt not in other.predicate_types:
                continue

            solver.reset()
            solver.add(other.to_z3(ctx))
            solver.add(self.to_z3(ctx))

            result = solver.check()
            # assert result != z3.unknown
            if result == z3.sat:
                return True
        else:
            return False

    def is_matched(self, value) -> bool:
        for pt in self.predicate_types:
            if pt == {PredicateType.Null}:
                continue
            if self.predicate_types == {PredicateType.Any}:
                return True

            solver = z3.Solver()
            ctx = VariableContext()
            var = ctx.get_variable(pt)
            solver.add(self.to_z3(ctx))
            solver.add(var == value)
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
