# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging

from errors.evaluator_errors import UnboundVariablesError


class PropertyEvaluator:
    def __init__(self, components, process_state, execution_state, timed_state):
        self._components = components
        self._process_state = process_state
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
    def _build_declarations(self, property):
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
            logging.error(f"Variales [ {variables} ] are not bound.")
            raise UnboundVariablesError()
        return declarations

    # Raises: UnboundVariablesError()
    # Propagates: ClockWasNotStartedError() from _build_time_assumption
    #             NoValueAssignedToVariableError() from _build_assumption
    def _build_assumptions(self, property, now):
        assumptions = []
        variables = list((property.variables()).keys())
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
            logging.error(f"Variales [ {variables} ] are not bound.")
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
