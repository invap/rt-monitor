# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import numpy as np

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    BuildSpecificationError,
    NoValueAssignedToVariableError,
    UnboundVariablesError, EvaluationError
)
from rt_monitor.logging_configuration import LoggingLevel
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


class PyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, execution_state, timed_state):
        super().__init__(components, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, now, prop):
        logging.log(LoggingLevel.ANALYSIS, f"Checking property {prop.name()}...")
        try:
            spec = self._build_spec(prop, now)
        except BuildSpecificationError:
            logging.error(f"Building specification for property [ {prop.name()} ] error.")
            raise EvaluationError()
        locs = {}
        # The formula is checked to be either true or false
        exec(spec, globals(), locs)
        result = locs['result']
        match result:
            case True:
                # If the formula is true, then the prop of interest passed.
                logging.log(LoggingLevel.ANALYSIS, f"Property {prop.name()} PASSED")
            case False:
                # If the formula is false, then the prop of interest failed.
                logging.log(LoggingLevel.ANALYSIS, f"Property {prop.name()} FAILED")
        if result == False:
            # Output counterexample as python program
            spec_filename = prop.name() + "@" + str(now) + ".py"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
            return PropertyEvaluator.PropertyEvaluationResult.FAILED
        else:
            return PropertyEvaluator.PropertyEvaluationResult.PASSED

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            # TODO: Add the possibility of having declarations.
            assumptions = self._build_assumptions(prop, now)
            spec = (f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"{prop.declarations()}\n\n"
                    f"result = {prop.formula()}\n")
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
        assumption = ""
        if isinstance(variable_value, np.ndarray):
            # The variable is of type np.ndarray, mainly used for implementing the internal structure
            # of digital twins
            # We assume that the instance has assigned values to all its components
            var_value_shape = variable_value.shape
            current = [0] * (len(var_value_shape) + 1)
            while PyPropertyEvaluator._more(current):
                value = PyPropertyEvaluator._get_value(variable_value, current)
                selector = PyPropertyEvaluator._build_selector(variable, current)
                assumption += f"{selector} = {value}\n"
                PyPropertyEvaluator._plus_one(var_value_shape, current)
        elif isinstance(variable_value, dict):
            # The variable is of type dict, used for monitoring arrays whose dimension is unknown by the monitor
            if not all([isinstance(x, NoValue) for x in variable_value.values()]):
                for key in variable_value:
                    # key if of the form [i0][i1]...[in]
                    assumption += f"{variable}{key} = {variable_value[key]}\n"
        else:
            # The variable is of one of the basic types supported expressed with a string
            if not isinstance(variable_value, NoValue):
                assumption = f"{variable} = {variable_value}\n"
        return assumption

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logging.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"

    @staticmethod
    def _build_selector(var_name, current):
        select = var_name
        for position in range(1, len(current)):
            select += f"[{current[position]}]"
        return select
