# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging
import toml

from rt_monitor.errors.framework_errors import FrameworkSpecificationError, PropertySpecificationError


class Property:
    def __init__(self, property_name, property_format, variables, declarations, formula):
        self._property_name = property_name
        self._format = property_format
        self._variables = variables
        self._declarations = declarations
        self._formula = formula

    def name(self):
        return self._property_name

    def format(self):
        return self._format

    def variables(self):
        return self._variables

    def declarations(self):
        return self._declarations

    def formula(self):
        return self._formula

    @staticmethod
    # Raises: PropertySpecificationError()
    def property_from_file(property_name, file_name):
        try:
            property_dict = toml.load(file_name)
        except FileNotFoundError:
            logging.error(f"Property file [ {file_name} ] not found.")
            raise FrameworkSpecificationError()
        except toml.TomlDecodeError as e:
            logging.error(
                f"TOML decoding of file [ {file_name} ] failed in [ line {e.lineno}, column {e.colno} ].")
            raise FrameworkSpecificationError()
        except PermissionError:
            logging.error(
                f"Permissions error opening file [ {file_name} ].")
            raise FrameworkSpecificationError()
        try:
            return Property.property_from_toml_dict(property_name, property_dict)
        except PropertySpecificationError:
            logging.error(f"Property specification error in property [ {property_name} ].")

    @staticmethod
    # Raises: PropertySpecificationError()
    def property_from_toml_dict(property_name, property_dict):
        if "format" not in property_dict:
            logging.error(f"Property must have a declared format.")
            raise PropertySpecificationError()
        if property_dict["format"] not in {"smt2", "sympy", "py"}:
            logging.error(f"Property format [ {property_dict["format"]} ] unknown.")
            raise PropertySpecificationError()
        if "formula" not in property_dict:
            logging.error(f"Property specification for [ {property_name} ] not found.")
            raise PropertySpecificationError()
        if "variables" not in property_dict:
            variables = {}
        else:
            variables = Property.build_variable_declarations(property_dict["variables"])
        if "declarations" not in property_dict:
            declarations = ""
        else:
            declarations = property_dict["declarations"]
        return Property(property_name, property_dict["format"], variables, declarations, property_dict["formula"])

    @staticmethod
    def build_variable_declarations(property_variables):
        variable_decls = {}
        split_property_variables = property_variables.split(",")
        if split_property_variables[0] != "None":
            for variable_name_class_type_with_parenthesis in split_property_variables:
                variable_name_class_type = variable_name_class_type_with_parenthesis.removeprefix("(").removesuffix(")")
                split_variable_name_class_type = variable_name_class_type.split(" ", 1)
                split_variable_name_class = split_variable_name_class_type[0].split(":")
                variable_decls[split_variable_name_class[0]] = (split_variable_name_class[1], split_variable_name_class_type[1])
        return variable_decls
