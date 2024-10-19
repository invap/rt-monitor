# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class FunctionNotImplemented(Exception):
    def __init__(self, function_name):
        super().__init__()
        self._function_name = function_name

    def get_function_name(self):
        return self._function_name


class EventLogFileMissing(Exception):
    def __init__(self, filename):
        super().__init__()
        self._filename = filename

    def get_filename(self):
        return self._filename


class FormulaError(Exception):
    def __init__(self, formula):
        super().__init__()
        self._formula = formula

    def get_formula(self):
        return self._formula


class AnalysisFailed(Exception):
    pass


class AbortRun(Exception):
    pass
