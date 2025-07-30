from typing import TYPE_CHECKING
from uuid import uuid4

import z3

from core.predicates.context.json_datatype import JsonDatatypeWrapper, build_json_datatype
from core.predicates.context.predicate_limitations import PredicateLimitations

if TYPE_CHECKING:
    from core.predicates.context.variable_context import VariableContext


class MainContext:
    def __init__(self, max_nesting_level: int) -> None:
        from core.predicates.context.variable_context import VariableContext

        self._z3_context = z3.Context()
        self._max_nesting_level = max_nesting_level
        self._json_types = build_json_datatype(
            z3_context=self._z3_context,
            level=0,
            max_nesting_level=self._max_nesting_level,
        )
        self._limitations = None
        self._root_var_ctx = VariableContext(main_context=self, level=-1)
        self._user_variables = {}
        self._all_object_keys_var = z3.Const(
            f'all_object_keys_{uuid4()}', z3.SeqSort(z3.StringSort(ctx=self._z3_context))
        )
        self._real_user_variables: dict[str, list[VariableContext]] = {}

    def get_all_object_keys_var(self):
        return self._all_object_keys_var

    def get_or_create_user_variable(self, name: str) -> 'VariableContext':
        from core.predicates.context.variable_context import VariableContext

        if name not in self._user_variables.keys():
            self._user_variables[name] = VariableContext(
                main_context=self,
                level=0,
                parent=self._root_var_ctx,
            )
        return self._user_variables[name]

    @property
    def max_nesting_level(self):
        return self._max_nesting_level

    @property
    def root_variable_context(self):
        return self._root_var_ctx

    def __del__(self):
        del self._z3_context
        if self._limitations is not None:
            del self._limitations

    @property
    def z3_context(self):
        return self._z3_context

    def set_limitations(self, limitations: PredicateLimitations) -> None:
        self._limitations = limitations

    @property
    def AllJsonTypes(self):
        return self._json_types

    def get_json_type(self, level: int) -> z3.DatatypeRef:
        return self._json_types[level]

    def wrap_json_type_variable(self, variable, level: int) -> JsonDatatypeWrapper:
        return JsonDatatypeWrapper(variable, self._json_types[level], self._z3_context)

    def create_json_type_variable(self, level: int) -> JsonDatatypeWrapper:
        return JsonDatatypeWrapper(
            z3.Const(f'var_{level}_{uuid4()}', self._json_types[level]),
            self._json_types[level],
            self.z3_context,
        )

    @property
    def limitations(self) -> PredicateLimitations:
        assert self._limitations is not None, "Context limitations are not initialized yet."
        return self._limitations
