import json

import z3

from core.predicates.context.main_context import MainContext
from core.predicates.context.variable_context import VariableContext


class _Unset:
    pass


class ResultContext:
    def __init__(self):
        self._user_variables = {}
        self._result = _Unset

    def reset(self):
        self._user_variables.clear()
        self._result = _Unset

    def calculate(self, z3_solver: z3.Solver, main_context: MainContext, operation_context: VariableContext):
        if z3_solver.check() != z3.sat:
            return

        for name, var_ctxs in main_context._real_user_variables.items():
            variants = []
            if name in self._user_variables.keys():
                variants.append(self._user_variables[name])
            for var_ctx in var_ctxs:
                variants.append(var_ctx.to_possible_value(z3_solver))
            variants.sort(key=lambda x: json.dumps(x, default=str))
            self._user_variables[name] = variants[0]

        if self._result is not _Unset:
            result_variants = [operation_context.to_possible_value(z3_solver), self._result]
            result_variants.sort(key=lambda x: json.dumps(x, default=str))
            self._result = result_variants[0]
        else:
            self._result = operation_context.to_possible_value(z3_solver)

    def get_user_var_value(self, var_name: str):
        return self._user_variables[var_name]

    def has_result(self):
        return self._result is not _Unset

    def get_result(self):
        return self._result
