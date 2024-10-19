# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class VariableException(Exception):
    def __init__(self, var_names):
        super().__init__()
        self._var_names = var_names

    def variable_names(self):
        return self._var_names


class UndeclaredComponentVariable(VariableException):
    def __init__(self, var_name):
        super().__init__(var_name)


class UnknownVariableClass(VariableException):
    def __init__(self, var_name, var_class):
        super().__init__(var_name)
        self._var_class = var_class

    def variable_class(self):
        return self._var_class


class UndeclaredVariable(VariableException):
    def __init__(self, var_name):
        super().__init__(var_name)


class UnboundVariables(VariableException):
    def __init__(self, var_names):
        super().__init__(var_names)


class NoValueAssignedToVariable(VariableException):
    def __init__(self, var_names):
        super().__init__(var_names)


class VariableTypeError(VariableException):
    def __init__(self, var_name):
        super().__init__(var_name)


class UnsupportedVariableType(VariableTypeError):
    def __init__(self, var_name, var_type):
        super().__init__(var_name)
        self._var_type = var_type

    def variable_type(self):
        return self._var_type

    @staticmethod
    def formula_type():
        raise NotImplementedError

class UnsupportedSMT2VariableType(UnsupportedVariableType):
    def __init__(self, var_name, var_type):
        super().__init__(var_name, var_type)

    @staticmethod
    def formula_type():
        return "SMT2"


class UnsupportedSymPyVariableType(UnsupportedVariableType):
    def __init__(self, var_name, var_type):
        super().__init__(var_name, var_type)

    @staticmethod
    def formula_type():
        return "SymPy"


class UnsupportedPyVariableType(UnsupportedVariableType):
    def __init__(self, var_name, var_type):
        super().__init__(var_name, var_type)

    @staticmethod
    def formula_type():
        return "Python"
