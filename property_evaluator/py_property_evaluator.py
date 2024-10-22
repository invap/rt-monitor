# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from typing import Iterable

from errors.clock_errors import ClockWasNotStartedError
from errors.evaluator_errors import (
    BuildSpecificationError,
    NoValueAssignedToVariableError, UnboundVariablesError, EvaluationError
)
from novalue import NoValue
from property_evaluator.property_evaluator import PropertyEvaluator


class PyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, prop, now):
        try:
            spec = self._build_spec(prop, now)
        except BuildSpecificationError:
            logging.error(f"Building specification for property [ {prop.name()} ] error.")
            raise EvaluationError()
        filename = prop.filename()
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

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            assumptions = self._build_assumptions(prop, now)
            spec = (f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {prop.formula()}\n")
            return spec
        except NoValueAssignedToVariableError:
            pass
        except UnboundVariablesError:
            pass
        except ClockWasNotStartedError:
            pass
        raise BuildSpecificationError()

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, Iterable):
            if any([isinstance(x, NoValue) for x in variable_value]):
                logging.error(f"No value [ {variable} ] has not been assigned a value.")
                raise NoValueAssignedToVariableError()
        elif isinstance(variable_value, NoValue):
            logging.error(f"No value [ {variable} ] has not been assigned a value.")
            raise NoValueAssignedToVariableError()
        # The variable has a value assigned.
        return f"{variable} = {variable_value}"

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logging.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"
