from copy import deepcopy
from enum import Enum
from typing import Any

from pydantic import Field

from schemas import BaseSchema


class VariableScope(Enum):
    GLOBAL = 'GLOBAL'
    LOCAL = 'LOCAL'


class Variable(BaseSchema):
    name: str
    scope: VariableScope = VariableScope.LOCAL
    pattern: str = '.+'
    default: str | int | dict | list | None = None


class VariablesGroup(BaseSchema):
    variables: list[Variable] = Field(default_factory=list)
    crud_operation_id: str | None = None
    crud_key: list[str] | None = None


class VariablesContext:
    def __init__(self, variables_group: VariablesGroup) -> None:
        self._variables_group = variables_group
        self._variables = {}

    @property
    def variables(self) -> dict:
        return deepcopy(self._variables)

    @property
    def variables_group(self) -> VariablesGroup:
        return self._variables_group

    def get(self, variable_name: str) -> Any:
        return self._variables.get(variable_name)

    def set(self, variable_name: str, value: Any) -> bool:
        if variable_name in self._variables.keys():
            if self._variables[variable_name] == value:
                return True
            else:
                return False
        else:
            self._variables[variable_name] = value
            return True


def variables_context_transaction(fn):
    def wrapper(*args, context: VariablesContext, **kwargs):
        orig_context = deepcopy(context._variables)
        try:
            res = fn(*args, context=context, **kwargs)
        except Exception:
            context._variables.clear()
            for k, v in orig_context.items():
                context._variables[k] = v
            raise
        if res is False:
            context._variables.clear()
            for k, v in orig_context.items():
                context._variables[k] = v
        return res

    return wrapper
