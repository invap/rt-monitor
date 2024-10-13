# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import os
from collections.abc import Iterable

from workflow_runtime_verification.clock_errors import ClockWasNotStarted
from workflow_runtime_verification.errors import (
    NoValueAssignedToVariable,
    UnboundVariables,
    FormulaError
)
from workflow_runtime_verification.specification.Py_interpreted_property import PyInterpretedProperty
from workflow_runtime_verification.specification.logic_property import LogicProperty
from workflow_runtime_verification.specification.novalue import NoValue
from workflow_runtime_verification.specification.specification_errors import UnsupportedSymPyVariableType


class SymPyProperty(PyInterpretedProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    @staticmethod
    def property_from_file(file_name, specification_file_directory):
        file_name_ext = file_name + ".protosympy"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        variables, formula = LogicProperty.prespec_from_file(file_path)
        return SymPyProperty(variables, formula, file_name)

    def _build_spec(self, component_dictionary, execution_state, timed_state, now):
        try:
            declarations = self._build_declarations(component_dictionary, execution_state, timed_state)
            assumptions = self._build_assumptions(component_dictionary, execution_state, timed_state, now)
            spec = (f"from sympy import Symbol\n" +
                    f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {self.formula()}\n")
            return spec
        except UnsupportedSymPyVariableType as e:
            logging.error(
                f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                f"{e.get_formula_type()} formula [ {self.filename()} ].")
            raise FormulaError(self.formula())
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ]  in formula [ {self.filename()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ].")
            raise FormulaError(self.formula())

    @staticmethod
    def _build_declaration(variable, variable_type):
        match variable_type:
            case "Bool":
                return f"{variable} = Symbol('{variable}')"
            case "Int":
                return f"{variable} = Symbol('{variable}', integer=True)"
            case "Real":
                return f"{variable} = Symbol('{variable}', real=True)"
            case _:
                raise UnsupportedSymPyVariableType(variable, variable_type)

