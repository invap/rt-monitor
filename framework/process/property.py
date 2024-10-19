# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class Property:
    def __init__(self, property_name, variables, formula, filename):
        self._property_name = property_name
        self._filename = filename
        self._variables = variables
        self._formula = formula

    def name(self):
        return self._property_name

    def filename(self):
        return self._filename

    def variables(self):
        return self._variables

    def formula(self):
        return self._formula

    def eval(self, components, execution_state, timed_state, now):
        raise NotImplementedError

    @staticmethod
    def property_from_file(property_name, file_name):
        raise NotImplementedError

    @staticmethod
    def property_from_str(property_name, property_variables, property_formula):
        raise NotImplementedError

    @staticmethod
    def preproperty_from_file(file_path):
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
    def preproperty_from_str(property_variables, property_formula):
        variable_decls = {}
        split_property_variables = property_variables.split(",")
        if split_property_variables[0] != "None":
            for variable_name_class_type_with_parenthesis in split_property_variables:
                variable_name_class_type = variable_name_class_type_with_parenthesis.removeprefix("(").removesuffix(")")
                split_variable_name_class_type = variable_name_class_type.split(" ", 1)
                split_variable_name_class = split_variable_name_class_type[0].split(":")
                variable_decls[split_variable_name_class[0]] = (split_variable_name_class[1], split_variable_name_class_type[1])
        return variable_decls, property_formula

    def format(self):
        raise NotImplementedError
