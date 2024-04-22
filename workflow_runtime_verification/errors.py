class PropertyTypeError(Exception):
    def __init__(self, property_type, filename):
        super().__init__()
        self._property_type = property_type
        self._filename = filename

    def property_type(self):
        return self._property_type

    def filename(self):
        return self._filename


class InvalidEventE(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def event(self):
        return self._event


class VariableException(Exception):
    def __init__(self, varnames):
        super().__init__()
        self._varnames = varnames

    def get_varnames(self):
        return self._varnames


class UndeclaredVariable(VariableException):
    def __init__(self, varname):
        super().__init__(varname)


class UnboundVariables(VariableException):
    def __init__(self, varnames):
        super().__init__(varnames)


class AlreadyDeclaredVariable(VariableException):
    def __init__(self, var_names):
        super().__init__(var_names)


class NoValueAssignedToVariable(VariableException):
    def __init__(self, var_names):
        super().__init__(var_names)


class ClockException(Exception):
    def __init__(self, clockname):
        super().__init__()
        self._clockname = clockname

    def get_clockname(self):
        return self._clockname


class AlreadyDeclaredClock(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class UndeclaredClock(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasNotStarted(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasAlreadyStarted(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasAlreadyPaused(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasNotPaused(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class NoValue:
    pass


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
    def __init__(self, device_name):
        super().__init__()
        self._device_name = device_name

    def get_device_name(self):
        return self._device_name


class FunctionNotImplemented(Exception):
    def __init__(self, function_name):
        super().__init__()
        self._function_name = function_name

    def get_function_name(self):
        return self._function_name


class FormulaError(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula


class EventError(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def get_event(self):
        return self._event


class AbortRun(Exception):
    pass


class NotImplementedPropertyType(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula
