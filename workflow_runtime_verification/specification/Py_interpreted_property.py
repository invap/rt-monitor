# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from collections.abc import Iterable

from workflow_runtime_verification.clock_errors import ClockWasNotStarted
from workflow_runtime_verification.errors import (
    NoValueAssignedToVariable,
    FormulaError,
    UnboundVariables
)
from workflow_runtime_verification.specification.logic_property import LogicProperty
from workflow_runtime_verification.specification.novalue import NoValue
from workflow_runtime_verification.specification.specification_errors import (
    UnsupportedPyVariableType,
    UnsupportedSymPyVariableType
)


class PyInterpretedProperty(LogicProperty):
    def __init__(self, property_name, variables, formula, filename):
        super().__init__(property_name, variables, formula, filename)

    def eval(self, component_dictionary, execution_state, timed_state, now):
        spec = self._build_spec(component_dictionary, execution_state, timed_state, now)
        filename = self.filename()
        locs = {}
        exec(spec, globals(), locs)
        negation_is_true = locs['result']
        if negation_is_true:
            # Output counterexample as toml_tasks_list
            spec_filename = filename + "@" + str(now) + ".py"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_true

    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, Iterable):
            if any([isinstance(x, NoValue) for x in variable_value]):
                raise NoValueAssignedToVariable(variable)
        elif isinstance(variable_value, NoValue):
            raise NoValueAssignedToVariable(variable)
        # The variable has a value assigned.
        return f"{variable} = {variable_value}"

    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            raise ClockWasNotStarted(variable)
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"
