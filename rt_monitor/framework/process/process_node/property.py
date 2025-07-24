# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import tomllib
import logging
# Create a logger for the proporty component
logger = logging.getLogger(__name__)

from rt_monitor.errors.process_errors import (
    PropertySpecificationError,
    VariableSpecificationError
)


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
    def property_from_toml_dict(property_name, prop_dict, files_path):
        # Decoding source for formula
        if "file" not in prop_dict and "formula" not in prop_dict:
            logger.error(f"Property [ {property_name} ] source not found.")
            raise PropertySpecificationError()
        if "formula" in prop_dict:
            # This operation might raise a PropertySpecificationError exception.
            return Property._property_from_toml_dict(prop_dict["name"], prop_dict)
        else:  # "file" in prop_dict
            file_name = prop_dict["file"] \
                if prop_dict["file"][0] == "/" or prop_dict["file"][0] == "." \
                else files_path + prop_dict["file"]
            # This operation might raise a PropertySpecificationError exception.
            return Property._property_from_file(property_name, file_name)

    @staticmethod
    # Raises: PropertySpecificationError()
    def _property_from_file(property_name, file_name):
        try:
            f = open(file_name, "rb")
        except FileNotFoundError:
            logger.error(f"Property file [ {file_name} ] not found.")
            raise PropertySpecificationError()
        except PermissionError:
            logger.error(f"Permissions error opening file [ {file_name} ].")
            raise PropertySpecificationError()
        except IsADirectoryError:
            logger.error(f"[ {file_name} ] is a directory and not a file.")
            raise PropertySpecificationError()
        try:
            property_dict = tomllib.load(f)
        except tomllib.TOMLDecodeError:
            logger.error(f"TOML decoding of file [ {file_name} ] failed.")
            raise PropertySpecificationError()
        # This operation might raise a PropertySpecificationError exception.
        return Property._property_from_toml_dict(property_name, property_dict)

    @staticmethod
    # Raises: PropertySpecificationError()
    def _property_from_toml_dict(property_name, prop_dict):
        # Decoding formula
        if "format" not in prop_dict:
            logger.error(f"Property must have a declared format.")
            raise PropertySpecificationError()
        if prop_dict["format"] not in {"smt2", "sympy", "py"}:
            logger.error(f"Property format [ {prop_dict["format"]} ] unknown.")
            raise PropertySpecificationError()
        # Decoding variables
        if "variables" not in prop_dict:
            variables = {}
        else:
            try:
                variables = Property.build_variable_declarations(prop_dict["variables"])
            except VariableSpecificationError:
                logger.error(f"Property variable declarations error.")
                raise PropertySpecificationError()
        # Decoding additional declarations
        if "declarations" not in prop_dict:
            declarations = ""
        else:
            declarations = prop_dict["declarations"]
        # Decoding additional declarations
        if "formula" not in prop_dict:
            logger.error(f"Property formula not found.")
            raise PropertySpecificationError()
        else:
            formula = prop_dict["formula"]
        return Property(property_name, prop_dict["format"], variables, declarations, formula)

    @staticmethod
    def build_variable_declarations(property_variables):
        # variable_decls is a dictionary whose keys are variable names and value is its class {State, Clock, Component}
        # and type {Int, Real, (Array Int ?)}
        variable_decls = {}
        split_property_variables = property_variables.split(",")
        for variable_name_class_type_with_parenthesis in split_property_variables:
            variable_name_class_type = variable_name_class_type_with_parenthesis.removeprefix("(").removesuffix(")")
            split_variable_name_class_type = variable_name_class_type.split(" ", 1)
            if not len(split_variable_name_class_type) == 2:
                logger.error(f"Incorrect variable declaration [ {variable_name_class_type_with_parenthesis} ] "
                              f"should be ([variable_name]:[variable_class] [variable_type]).")
                raise VariableSpecificationError()
            variable_type = split_variable_name_class_type[1]
            # TODO: check integrity of the variable type in variable_type; if not OK raise
            #  VariableSpecificationError exception.
            split_variable_name_class = split_variable_name_class_type[0].split(":")
            variable_name = split_variable_name_class[0]
            variable_class = split_variable_name_class[1]
            if variable_class not in {"Component", "State", "Clock"}:
                logger.error(
                    f"Variables class [ {variable_class} ] unsupported.")
                raise VariableSpecificationError()
            variable_decls[variable_name] = (variable_class, variable_type)
        return variable_decls
