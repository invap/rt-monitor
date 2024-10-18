# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
from workflow_runtime_verification.errors import UnboundVariables


class LogicProperty:
    def __init__(self, property_name, variables, formula, filename):
        self._property_name = property_name
        self._filename = filename
        self._variables = variables
        self._formula = formula

    def property_name(self):
        return self._property_name

    def filename(self):
        return self._filename

    def variables(self):
        return self._variables

    def formula(self):
        return self._formula

    def eval(self, component_dictionary, execution_state, timed_state, now):
        raise NotImplementedError

    @staticmethod
    def property_from_file(property_name, file_name):
        raise NotImplementedError

    @staticmethod
    def property_from_str(property_name, property_variables, property_formula):
        raise NotImplementedError

    @staticmethod
    def prespec_from_file(file_path):
        with (open(file_path, "r") as file):
            variable_decls = {}
            split_readline = (file.readline().split("\n")[0]).split(",")
            if split_readline[0] != "None":
                for variable_name_class_type_with_parenthesis in split_readline:
                    variable_name_class_type = variable_name_class_type_with_parenthesis.removeprefix("(").removesuffix(")")
                    split_variable_name_class_type = variable_name_class_type.split(" ", 1)
                    split_variable_name_class = split_variable_name_class_type[0].split(":")
                    variable_decls[split_variable_name_class[0]] = (split_variable_name_class[1], split_variable_name_class_type[1])
            formula = ""
            for line in file:
                formula = formula + line
        file.close()
        return variable_decls, formula

    @staticmethod
    def prespec_from_str(property_variables, property_formula):
        variable_decls = {}
        split_property_variables = property_variables.split(",")
        if split_property_variables[0] != "None":
            for variable_name_class_type_with_parenthesis in split_property_variables:
                variable_name_class_type = variable_name_class_type_with_parenthesis.removeprefix("(").removesuffix(")")
                split_variable_name_class_type = variable_name_class_type.split(" ", 1)
                split_variable_name_class = split_variable_name_class_type[0].split(":")
                variable_decls[split_variable_name_class[0]] = (split_variable_name_class[1], split_variable_name_class_type[1])
        return variable_decls, property_formula

    def _build_spec(self, component_dictionary, execution_state, timed_state, now):
        raise NotImplementedError

    def _build_declarations(self, component_dictionary, execution_state, timed_state):
        declarations = []
        variables = list((self.variables()).keys())
        # building declarations for variables in the components state
        for component in component_dictionary:
            dictionary = component_dictionary[component].state()
            for variable in dictionary:
                if variable in variables:
                    declarations.append(self._build_declaration(variable, self.variables()[variable][1]))
                    variables.remove(variable)
        # building declarations for variables in the execution state
        for variable in execution_state:
            if variable in variables:
                declarations.append(self._build_declaration(variable, self.variables()[variable][1]))
                variables.remove(variable)
        # building declarations for clocks in the timed state
        for variable in timed_state:
            if variable in variables:
                declarations.append(self._build_declaration(variable, self.variables()[variable][1]))
                variables.remove(variable)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return declarations

    def _build_assumptions(self, component_dictionary, execution_state, timed_state, now):
        assumptions = []
        variables = list((self.variables()).keys())
        # building assumptions for variables in the components state
        for component in component_dictionary:
            dictionary = component_dictionary[component].state()
            for variable in dictionary:
                if variable in variables:
                    assumptions.append(self._build_assumption(variable, dictionary[variable][1]))
                    variables.remove(variable)
        # building assumptions for variables in the execution state
        for variable in execution_state:
            if variable in variables:
                assumptions.append(self._build_assumption(variable, execution_state[variable][1]))
                variables.remove(variable)
        # building assumptions for clocks in the timed state
        for variable in timed_state:
            if variable in variables:
                assumptions.append(self._build_time_assumption(variable, timed_state[variable][1], now))
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

