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

    def eval_with(self, monitor, now):
        raise NotImplementedError


class SMT2Property(LogicProperty):
    def __init__(self, variables, formula, filename):
        super().__init__(variables, formula, filename)

    def eval_with(self, event_time, monitor):
        return monitor.eval_smt2(event_time, self)


class SymPyProperty(LogicProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    def eval_with(self, event_time, monitor):
        return monitor.eval_py(event_time,
                               monitor.sympy_build_spec(event_time, self),
                               self.filename())


class PyProperty(LogicProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    def eval_with(self, event_time, monitor):
        return monitor.eval_py(event_time,
                               monitor.py_build_spec(event_time, self),
                               self.filename())
