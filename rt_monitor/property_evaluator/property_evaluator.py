# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from enum import Enum

from rt_monitor.errors.evaluator_errors import UnboundVariablesError


class PropertyEvaluator:
    class PropertyEvaluationResult (Enum):
        PASSED = "PASSED"
        FAILED = "FAILED"

    def __init__(self, components, execution_state, timed_state):
        self._components = components
        self._execution_state = execution_state
        self._timed_state = timed_state

    # Raises: EvaluationError()
    def eval(self, prop, now):
        raise NotImplementedError

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        raise NotImplementedError

    # Raises: UnboundVariablesError()
    # Propagates: UnsupportedVariableTypeError() from _build_declaration
    def _build_variable_declarations(self, property):
        declarations = []
        variables = list((property.variables()).keys())
        # building declarations for variables in the components state
        for component in self._components:
            dictionary = self._components[component].state()
            for variable in dictionary:
                if variable in variables:
                    declarations.append(self._build_declaration(variable, property.variables()[variable][1]))
                    variables.remove(variable)
        # building declarations for variables in the execution state
        for variable in self._execution_state:
            if variable in variables:
                declarations.append(self._build_declaration(variable, property.variables()[variable][1]))
                variables.remove(variable)
        # building declarations for clocks in the timed state
        for variable in self._timed_state:
            if variable in variables:
                declarations.append(self._build_declaration(variable, property.variables()[variable][1]))
                variables.remove(variable)
        if len(variables) != 0:
            logging.error(f"Variables [ {variables} ] are not bound.")
            raise UnboundVariablesError()
        return declarations

    # Raises: UnboundVariablesError()
    # Propagates: ClockWasNotStartedError() from _build_time_assumption
    #             NoValueAssignedToVariableError() from _build_assumption
    def _build_assumptions(self, prop, now):
        assumptions = []
        variables = list((prop.variables()).keys())
        # building assumptions for variables in the components state
        for component in self._components:
            dictionary = self._components[component].state()
            for variable in dictionary:
                if variable in variables:
                    assumptions.append(self._build_assumption(variable, dictionary[variable][1]))
                    variables.remove(variable)
        # building assumptions for variables in the execution state
        for variable in self._execution_state:
            if variable in variables:
                assumptions.append(self._build_assumption(variable, self._execution_state[variable][1]))
                variables.remove(variable)
        # building assumptions for clocks in the timed state
        for variable in self._timed_state:
            if variable in variables:
                assumptions.append(self._build_time_assumption(variable, self._timed_state[variable][1], now))
                variables.remove(variable)
        if len(variables) != 0:
            logging.error(f"Variables [ {variables} ] are not bound.")
            raise UnboundVariablesError()
        return assumptions

    # Raises: UnsupportedVariableTypeError()
    @staticmethod
    def _build_declaration(variable, variable_type):
        raise NotImplementedError

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        raise NotImplementedError

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        raise NotImplementedError

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
                    PropertyEvaluator._plus_one_in_position(shape_, current, position - 1)
                    carry = 0

    @staticmethod
    def _plus_one(shape_, current):
        PropertyEvaluator._plus_one_in_position(shape_, current, len(current) - 1)

    @staticmethod
    def _more(current):
        return current[0] == 0

    @staticmethod
    def _get_value(array_value, current):
        value = array_value
        for position in range(1, len(current)):
            value = value[current[position]]
        return value

