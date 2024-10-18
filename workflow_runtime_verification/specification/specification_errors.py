# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class UnsupportedNodeType(Exception):
    def __init__(self, node_type):
        super().__init__()
        self._node_type = node_type

    def get_node_type(self):
        return self._node_type


class NotImplementedPropertyType(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula


class VariableTypeError(Exception):
    def __init__(self):
        super().__init__()


class UnsupportedVariableType(VariableTypeError):
    def __init__(self, varname, vartype):
        super().__init__()
        self._varname = varname
        self._vartype = vartype

    def get_variable_type(self):
        return self._vartype

    def get_variable_name(self):
        return self._varname


class UnsupportedSMT2VariableType(UnsupportedVariableType):
    def __init__(self, varname, vartype):
        super().__init__(varname, vartype)

    @staticmethod
    def get_formula_type():
        return "SMT2"


class UnsupportedSymPyVariableType(UnsupportedVariableType):
    def __init__(self, varname, vartype):
        super().__init__(varname, vartype)

    @staticmethod
    def get_formula_type():
        return "SymPy"


class UnsupportedPyVariableType(UnsupportedVariableType):
    def __init__(self, varname, vartype):
        super().__init__(varname, vartype)

    @staticmethod
    def get_formula_type():
        return "Python"


class PropertySourceError(Exception):
    def __init__(self):
        super().__init__()


class PropertyFormatError(Exception):
    def __init__(self, property_format):
        super().__init__()
        self._property_format = property_format

    def property_format(self):
        return self._property_format


