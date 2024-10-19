# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
from errors.variable_errors import UnboundVariables


class PropertyEvaluator:
    def __init__(self, components, process_state, execution_state, timed_state):
        self._components = components
        self._process_state = process_state
        self._execution_state = execution_state
        self._timed_state = timed_state

    def eval(self, property, now):
        raise NotImplementedError

    def _build_spec(self, property, now):
        raise NotImplementedError

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
            raise UnboundVariables(str(variables))
        return declarations

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
            raise UnboundVariables(str(variables))
        return assumptions

    @staticmethod
    def _build_declaration(variable, variable_type):
        raise NotImplementedError

    @staticmethod
    def _build_assumption(variable, variable_value):
        raise NotImplementedError

    @staticmethod
    def _build_time_assumption(variable, clock, now):
        raise NotImplementedError
