# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class LogicProperty:
    def __init__(self, variables, formula, filename):
        self._filename = filename
        self._variables = variables
        self._formula = formula

    def filename(self):
        return self._filename

    def variables(self):
        return self._variables

    def formula(self):
        return self._formula

    def eval(self, event_time, component_dictionary, timed_state, execution_state):
        raise NotImplementedError

    @staticmethod
    def property_from_file(file_name, specification_file_directory):
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
