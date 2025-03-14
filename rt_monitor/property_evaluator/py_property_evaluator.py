# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging
import numpy as np

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    BuildSpecificationError,
    NoValueAssignedToVariableError, UnboundVariablesError, EvaluationError
)
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


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
        locs = {}
        exec(spec, globals(), locs)
        negation_is_true = locs['result']
        if negation_is_true:
            # Output counterexample as toml_tasks_list
            spec_filename = prop.name() + "@" + str(now) + ".py"
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
        if isinstance(variable_value, np.ndarray):
            # The variable is of type np.ndarray, mainly used for implementing the internal structure
            # of digital twins
            if any([isinstance(x, NoValue) for x in variable_value]):
                logging.error(f"The variable [ {variable} ] has a member that has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
                # The instance has assigned values to all its components
                assumption = ""
                var_value_shape = variable_value.shape
                current = [0] * (len(var_value_shape) + 1)
                while PyPropertyEvaluator._more(current):
                    value = PyPropertyEvaluator._get_value(variable_value, current)
                    selector = PyPropertyEvaluator._build_selector(variable, current)
                    assumption += f"{selector} = {value}\n"
                    PyPropertyEvaluator._plus_one(var_value_shape, current)
                return assumption
        elif isinstance(variable_value, dict):
            # The variable is of type dict, used for monitoring arrays whose dimension is unknown by the monitor
            if any([isinstance(x, NoValue) for x in variable_value.values()]):
                logging.error(f"The variable [ {variable} ] has a member that has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
                # The instance has assigned values to all its components
                assumption = ""
                for key in variable_value:
                    # key if of the form [i0][i1]...[in]
                    assumption += f"{variable}{key} = {variable_value[key]}\n"
                return assumption
        else:
            # The variable is of one of the basic types supported expressed with a string
            if isinstance(variable_value, NoValue):
                logging.error(f"The variable [ {variable} ] has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
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
    def _plus_one_in_position(shape_, current, position):
        if position == 0:
            current[position] = 1
        else:
            carry = 1
            while carry == 1 and position > 0:
                new_value = (current[position] + 1) % shape_[position - 1]
                carry = (current[position] + 1) // shape_[position - 1]
                current[position] = new_value
                if current[position] == 0:
                    PyPropertyEvaluator._plus_one_in_position(shape_, current, position - 1)
                    carry = 0

    @staticmethod
    def _plus_one(shape_, current):
        PyPropertyEvaluator._plus_one_in_position(shape_, current, len(current) - 1)

    @staticmethod
    def _more(current):
        return current[0] == 0

    @staticmethod
    def _get_value(array_value, current):
        value = array_value
        for position in range(1, len(current)):
            value = value[current[position]]
        return value

    @staticmethod
    def _build_selector(var_name, current):
        select = var_name
        for position in range(1, len(current)):
            select += f"[{current[position]}]"
        return select
