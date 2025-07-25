from abc import ABC
from uuid import uuid4

import z3

from core.predicates.base_predicate import PredicateType
from core.predicates.context.json_datatype import JsonDatatypeWrapper
from core.predicates.context.main_context import MainContext


class _Undefined:
    pass


class BaseVariableContext(ABC):
    @property
    def is_root(self):
        return self._parent is None

    @property
    def main_context(self) -> MainContext:
        return self._main_context

    def get_limitations(self):
        return self._main_context.limitations.get_for_level(self._level)

    def __init__(self, main_context: MainContext, level: int = 0, parent=None) -> None:
        """Initialize variable context.

        :param level: Nesting level for JSON (None for max level)
        :type level: int | None

        .. Docstring generated by Gemini 2.5 Flash, modified by Gemini 2.5 Flash
        """

        if parent is None and level >= 0:
            self._parent = main_context.root_variable_context
            main_context.root_variable_context._children.append(self)
        else:
            self._parent = parent

        self._children: list[VariableContext] = []
        self._global_constraints = []
        self._var_type_constraints = {}
        self._main_context = main_context
        self._level = level

        if not self.is_root:
            self._json_var = main_context.create_json_type_variable(level=level)

    @property
    def level(self) -> int:
        return self._level

    @property
    def z3_context(self):
        return self._main_context.z3_context

    @property
    def JsonType(self):
        return self.main_context.get_json_type(level=self.level)

    @property
    def json_type_variable(self) -> JsonDatatypeWrapper:
        """Get JSON datatype variable.

        :return: JSON datatype instance
        :rtype: JsonDatatype

        .. Docstring generated by Gemini 2.5 Flash
        """
        return self._json_var

    def create_child_context(self) -> 'VariableContext':
        """Create nested variable context with reduced level.

        :return: New child context
        :rtype: VariableContext

        .. Docstring generated by Gemini 2.5 Flash, modified by Gemini 2.5 Flash
        """
        if self.is_root:
            new_child_context = VariableContext(level=0, parent=self, main_context=self._main_context)
        else:
            new_child_context = VariableContext(level=self._level + 1, parent=self, main_context=self._main_context)
        self._children.append(new_child_context)
        return new_child_context

    def create_sibling_context(self) -> 'VariableContext':
        return self._parent.create_child_context()

    @property
    def parent(self):
        return self._parent

    @property
    def root_parent(self):
        if self._parent is None:
            return self
        else:
            return self._parent.root_parent


# class EvaluateValueMixin(BaseVariableContext):
#     def __init__(self,  main_context: MainContext, level=0, parent=None) -> None:
#         super().__init__(main_context=main_context, level=level, parent=parent)
#         self._key_vars = []
#
#     def register_key_var(self, key_var):
#         self._key_vars.append(key_var)
#
#     def _get_all_possible_keys(self, solver):
#         results = [solver.model().eval(key_var, model_completion=True).as_string() for key_var in self._key_vars]
#         for child in self._children:
#             results += child._get_all_possible_keys(solver)
#         return results
#
#     def _guess_type(self, solver, var):
#         for level in reversed(range(100)):
#             try:
#                 json_var = JsonDatatype.from_var(self.z3_context, solver.model().eval(var, model_completion=True), level=level)
#                 solver.model().eval(
#                     json_var.is_object(),
#                     model_completion=True,
#                 )
#             except z3.Z3Exception:
#                 pass
#             else:
#                 fake_context = self.__class__()
#                 fake_context._json_var = json_var
#                 return fake_context.evaluate_value(solver)
#
#     def _calculate_var_values(self, solver: z3.Solver):
#         results = {}
#         for child in self._children:
#             results.update(child._calculate_var_values(solver))
#
#         raw_val = solver.model().eval(self._json_var.z3_variable, model_completion=True).ast.value
#
#         if solver.model().eval(self._json_var.is_int(), model_completion=True):
#             results[raw_val] = solver.model().eval(self._json_var.get_int(), model_completion=True).as_long()
#         if solver.model().eval(self._json_var.is_str(), model_completion=True):
#             results[raw_val] = solver.model().eval(self._json_var.get_str(), model_completion=True).as_string()
#         if solver.model().eval(self._json_var.is_real(), model_completion=True):
#             results[raw_val] = solver.model().eval(self._json_var.get_real(), model_completion=True).as_decimal(10)
#         if solver.model().eval(self._json_var.is_bool(), model_completion=True):
#             results[raw_val] = solver.model().eval(self._json_var.get_bool(), model_completion=True)
#         if solver.model().eval(self._json_var.is_object(), model_completion=True):
#             sub_result = {}
#             for key in self._get_all_possible_keys(solver):
#                 if key:
#                     var_id = solver.model().eval(z3.Select(self._json_var.get_object(), z3.StringVal(key, ctx=self.z3_context))).ast.value
#                     if var_id not in results.keys():
#                         guessed_type = self._guess_type(
#                             solver=solver,
#                             var=solver.model().eval(
#                                 z3.Select(self._json_var.get_object(), z3.StringVal(key, ctx=self.z3_context)),
#                                 model_completion=True,
#                             ),
#                         )
#                         if guessed_type is not _Undefined:
#                             sub_result[key] = guessed_type
#                     elif results[var_id] is not _Undefined:
#                         sub_result[key] = results[var_id]
#                 else:
#                     break
#             results[raw_val] = sub_result
#         if solver.model().eval(self._json_var.is_array(), model_completion=True):
#             sub_result = []
#             array_len = solver.model().eval(z3.Length(self._json_var.get_array()), model_completion=True).as_long()
#             for i in range(array_len):
#                 var_id = solver.model().eval(self._json_var.get_array()[i]).ast.value
#                 if var_id not in results.keys():
#                     sub_result.append(
#                         self._guess_type(
#                             solver=solver, var=solver.model().eval(self._json_var.get_array()[i], model_completion=True)
#                         )
#                     )
#                 else:
#                     sub_result.append(results[var_id])
#             results[raw_val] = sub_result
#         if solver.model().eval(self._json_var.is_null(), model_completion=True):
#             results[raw_val] = None
#         if solver.model().eval(self._json_var.is_undefined(), model_completion=True):
#             results[raw_val] = _Undefined
#
#         return results
#
#     def evaluate_value(self, solver: z3.Solver):
#         calculated_values = self._calculate_var_values(solver)
#         var_id = solver.model().eval(self._json_var.z3_variable, model_completion=True).ast.value
#         return calculated_values.get(var_id, _Undefined)  # known issue in some cases


class KeyVariablesMixin(BaseVariableContext):
    def __init__(self, main_context: MainContext, level: int = 0, parent=None) -> None:
        super().__init__(
            main_context=main_context,
            level=level,
            parent=parent,
        )
        self._key_vars = []

    def register_key_var(self, z3_var):
        self._key_vars.append(z3_var)

    def get_all_var_keys(self):
        all_keys = self._key_vars
        for child in self._children:
            all_keys += child.get_all_var_keys()
        return all_keys


class VariableContext(KeyVariablesMixin, BaseVariableContext):
    """Context manager for Z3 variables and constraints.

    Manages variable types, constraints, and nested contexts for predicate evaluation.

    .. Docstring created by Gemini 2.5 Flash, modified by DeepSeek-V3 (2024)
    """

    def __del__(self):
        for child in self._children:
            del child
        self._children.clear()
        if self._parent and self in self._parent._children:
            self._parent._children.remove(self)

    def set_as_user_variable(self, var: str | None):
        if var is not None:
            self.push_to_global_constraints(
                self.cast_to(0).json_type_variable.z3_variable
                == self._main_context.get_or_create_user_variable(var).json_type_variable.z3_variable
            )

    def push_to_global_constraints(self, expr: z3.ExprRef | bool) -> None:
        """Add constraint to global context.

        :param expr: Z3 expression or boolean to add
        :type expr: z3.ExprRef | bool

        .. Docstring created by Gemini 2.5 Flash
        """
        constraint_expression = expr
        self._global_constraints.append(constraint_expression)

    def get_variable(self, predicate_type: PredicateType):
        """Get variable cast to specified type with type constraint.

        :param predicate_type: Target predicate type
        :type predicate_type: PredicateType
        :return: Z3 variable of specified type
        :rtype: z3.ExprRef
        :raises NotImplementedError: For unsupported predicate types

        .. Docstring created by Gemini 2.5 Flash
        """
        if predicate_type not in self._var_type_constraints.keys():
            self._var_type_constraints[predicate_type] = self._json_var.is_expression_by_type(predicate_type)

        return self._json_var.get_expression_by_type(predicate_type)

    def get_all_contexts(self):
        return [self] + [child for child in self._children for child in child.get_all_contexts()]

    def pop_from_global_constraints(self) -> None:
        variable_type_expressions = list(self._var_type_constraints.values())
        if not variable_type_expressions:
            type_union_expression = z3.BoolVal(True, ctx=self.z3_context)
        else:
            type_union_expression = z3.PbEq([(v, 1) for v in variable_type_expressions], 1, ctx=self.z3_context)
        nested_context_constraints = [child.pop_from_global_constraints() for child in self._children]

        self._var_type_constraints.clear()

        # key vars
        all_keys_constraints = []

        if self.is_root:
            all_key_vars = self.get_all_var_keys()
            all_keys_seq = z3.Empty(z3.SeqSort(z3.StringSort(ctx=self.z3_context)))

            for var in all_key_vars:
                all_keys_seq = z3.Concat(all_keys_seq, z3.Unit(var))

            all_keys_constraints += [
                self.main_context.get_all_object_keys_var() == all_keys_seq,
            ]

        return z3.And(
            type_union_expression,
            *self._global_constraints,
            *nested_context_constraints,
            *all_keys_constraints,
            z3.BoolVal(True, ctx=self.z3_context),
        )

    @staticmethod
    def _cast_json_type_var(source_var, main_ctx, source_level, target_level):
        if source_level == target_level:
            return source_var, z3.BoolVal(True, ctx=main_ctx.z3_context)
        dts = main_ctx.AllJsonTypes

        new_var = z3.Const(f'var_{target_level}_{uuid4()}', dts[target_level])

        constraints = [
            z3.Implies(
                dts[source_level].is_bool(source_var),
                dts[target_level].get_bool(new_var) == dts[source_level].get_bool(source_var),
            ),
            z3.Implies(
                dts[source_level].is_int(source_var),
                dts[target_level].get_int(new_var) == dts[source_level].get_int(source_var),
            ),
            z3.Implies(
                dts[source_level].is_real(source_var),
                dts[target_level].get_real(new_var) == dts[source_level].get_real(source_var),
            ),
            z3.Implies(
                dts[source_level].is_str(source_var),
                dts[target_level].get_str(new_var) == dts[source_level].get_str(source_var),
            ),
        ]

        try:
            constraints += [
                dts[target_level].is_object(new_var) == dts[source_level].is_object(source_var),
                dts[target_level].is_array(new_var) == dts[source_level].is_array(source_var),
            ]
        except AttributeError:
            # dirty hack to stop on JsonType without is_object/is_array (end of nesting)
            try:
                constraints.append(dts[target_level].is_object(new_var) == z3.BoolVal(False, ctx=main_ctx.z3_context))
            except Exception:
                pass
            try:
                constraints.append(dts[target_level].is_array(new_var) == z3.BoolVal(False, ctx=main_ctx.z3_context))
            except Exception:
                pass
            try:
                constraints.append(
                    dts[source_level].is_object(source_var) == z3.BoolVal(False, ctx=main_ctx.z3_context)
                )
            except Exception:
                pass
            try:
                constraints.append(dts[source_level].is_array(source_var) == z3.BoolVal(False, ctx=main_ctx.z3_context))
            except Exception:
                pass

            return new_var, z3.And(*constraints)

        k = z3.String(f'k_{uuid4()}', ctx=main_ctx.z3_context)
        j = z3.Int(f'j_{uuid4()}', ctx=main_ctx.z3_context)

        def to_obj_subvar(object_iterator):
            sub_var, sub_constraints = VariableContext._cast_json_type_var(
                dts[source_level].get_object(source_var)[object_iterator], main_ctx, source_level + 1, target_level + 1
            )
            return z3.Implies(
                z3.Contains(main_ctx.get_all_object_keys_var(), z3.Unit(object_iterator)),
                z3.And(dts[target_level].get_object(new_var)[object_iterator] == sub_var, sub_constraints),
            )

        constraints += [
            z3.Implies(
                dts[source_level].is_object(source_var),
                z3.ForAll([k], to_obj_subvar(k)),
            ),
        ]

        #
        def to_arr_subvar(array_iterator):
            sub_var, sub_constraints = VariableContext._cast_json_type_var(
                dts[source_level].get_array(source_var)[j], main_ctx, source_level + 1, target_level + 1
            )
            return z3.Implies(
                z3.And(
                    array_iterator >= 0,
                    array_iterator < z3.Length(dts[source_level].get_array(source_var)),
                    z3.Length(dts[target_level].get_array(new_var))
                    == z3.Length(dts[source_level].get_array(source_var)),
                ),
                z3.And(
                    dts[target_level].get_array(new_var)[array_iterator] == sub_var,
                    sub_constraints,
                ),
            )

        constraints += [
            z3.Implies(dts[source_level].is_array(source_var), z3.ForAll([j], to_arr_subvar(j))),
        ]
        return new_var, z3.And(*constraints)

    def cast_to(self, target_level: int) -> 'VariableContext':
        if target_level == self.level:
            return self
        source_var = self._json_var.z3_variable

        new_context = self.root_parent.create_child_context()
        while target_level > new_context.level:
            new_context = new_context.create_child_context()

        new_var, new_var_constraint = self._cast_json_type_var(source_var, self._main_context, self.level, target_level)
        self.push_to_global_constraints(new_var_constraint)
        self.push_to_global_constraints(new_context.json_type_variable.z3_variable == new_var)

        return new_context
