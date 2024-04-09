class InvalidEventE(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def event(self):
        return self._event


class UndeclaredVariable(Exception):
    def __init__(self, varname):
        super().__init__()
        self._varname = varname

    def getVarname(self):
        return self._varname


class UnboundVariables(Exception):
    def __init__(self, vars):
        super().__init__()
        self._vars = vars

    def getVars(self):
        return self._vars


class AlreadyDeclaredVariable(Exception):
    def __init__(self, varname):
        super().__init__()
        self._varname = varname

    def getVarname(self):
        return self._varname


class AlreadyDeclaredClock(Exception):
    def __init__(self, clockname):
        super().__init__()
        self._clockname = clockname

    def getVarname(self):
        return self._clockname


class UndeclaredClock(Exception):
    def __init__(self, clockname):
        super().__init__()
        self._clockname = clockname

    def getVarname(self):
        return self._clockname


class NoValueAssignedToVariable(Exception):
    def __init__(self, varname):
        super().__init__()
        self._varname = varname

    def getVarname(self):
        return self._varname


class NoValue:
    pass


class AnalysisFailed(Exception):
    pass


class CheckpointDoesNotExist(Exception):
    def __init__(self, checkpoint_name):
        super().__init__()
        self._checkpoint_name = checkpoint_name

    def getCheckpointName(self):
        return self._checkpoint_name


class TaskDoesNotExist(Exception):
    def __init__(self, task_name):
        super().__init__()
        self._task_name = task_name

    def getTaskName(self):
        return self._task_name


class ComponentDoesNotExist(Exception):
    def __init__(self, device_name):
        super().__init__()
        self._device_name = device_name

    def getDeviceName(self):
        return self._device_name


class FunctionNotImplemented(Exception):
    def __init__(self, function_name):
        super().__init__()
        self._function_name = function_name

    def getFunctionName(self):
        return self._function_name


class FormulaError(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def getFormula(self):
        return self._formula


class EventError(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def getEvent(self):
        return self._event


class AbortRun(Exception):
    pass
