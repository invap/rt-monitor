# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class InvalidEventE(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def get_event(self):
        return self._event


class VariableException(Exception):
    def __init__(self, varnames):
        super().__init__()
        self._varnames = varnames

    def get_varnames(self):
        return self._varnames


class UndeclaredComponentVariable(VariableException):
    def __init__(self, varname):
        super().__init__(varname)


class UnknownVariableClass(VariableException):
    def __init__(self, varname, varclass):
        super().__init__(varname)
        self._varclass = varclass

    def get_varclass(self):
        return self._varclass


class UndeclaredVariable(VariableException):
    def __init__(self, varname):
        super().__init__(varname)


class UnboundVariables(VariableException):
    def __init__(self, varnames):
        super().__init__(varnames)


class NoValueAssignedToVariable(VariableException):
    def __init__(self, var_names):
        super().__init__(var_names)


class AnalysisFailed(Exception):
    pass


class CheckpointDoesNotExist(Exception):
    def __init__(self, checkpoint_name):
        super().__init__()
        self._checkpoint_name = checkpoint_name

    def get_checkpoint_name(self):
        return self._checkpoint_name


class TaskDoesNotExist(Exception):
    def __init__(self, task_name):
        super().__init__()
        self._task_name = task_name

    def get_task_name(self):
        return self._task_name


class ComponentDoesNotExist(Exception):
    def __init__(self, component_name):
        super().__init__()
        self._component_name = component_name

    def get_component_name(self):
        return self._component_name


class FunctionNotImplemented(Exception):
    def __init__(self, function_name):
        super().__init__()
        self._function_name = function_name

    def get_function_name(self):
        return self._function_name


class EventError(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def get_event(self):
        return self._event


class EventLogFileMissing(Exception):
    def __init__(self, filename):
        super().__init__()
        self._filename = filename

    def get_filename(self):
        return self._filename


class AbortRun(Exception):
    pass


class FormulaError(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula
