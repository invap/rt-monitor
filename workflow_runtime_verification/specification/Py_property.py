# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import os

from workflow_runtime_verification.errors import NoValueAssignedToVariable, FormulaError, UnboundVariables
from workflow_runtime_verification.specification.Py_interpreted_property import PyInterpretedProperty
from workflow_runtime_verification.specification.logic_property import LogicProperty


class PyProperty(PyInterpretedProperty):
    def __init__(self, property_name, variables, formula, filename):
        super().__init__(property_name, variables, formula, filename)

    def eval_with(self, event_time, monitor):
        return monitor.eval_py(event_time,
                               monitor.py_build_spec(event_time, self),
                               self.filename())

    @staticmethod
    def property_from_file(property_name, file_name):
        variables, spec = LogicProperty.prespec_from_file(file_name)
        return PyProperty(property_name, variables, spec, file_name)

    @staticmethod
    def property_from_str(property_name, property_variables, property_formula):
        variables, formula = LogicProperty.prespec_from_str(property_variables, property_formula)
        return PyProperty(property_name, variables, formula, "")

    def _build_spec(self, component_dictionary, execution_state, timed_state, now):
        try:
            assumptions = self._build_assumptions(component_dictionary, execution_state, timed_state, now)
            spec = (f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {self.formula()}\n")
            return spec
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ]")
            raise FormulaError(self.formula())

