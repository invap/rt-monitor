# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from typing import Iterable

from errors.clock_errors import ClockWasNotStarted
from errors.errors import FormulaError
from errors.variable_errors import NoValueAssignedToVariable, UnboundVariables
from novalue import NoValue
from property_evaluator.property_evaluator import PropertyEvaluator


class PyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    def eval(self, property, now):
        spec = self._build_spec(property, now)
        filename = property.filename()
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

    def _build_spec(self, property, now):
        try:
            assumptions = self._build_assumptions(property, now)
            spec = (f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {property.formula()}\n")
            return spec
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.variable_names()} ] has no value.")
            raise FormulaError(property.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.variable_names()} ] in formula [ {property.filename()} ]")
            raise FormulaError(property.formula())

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
