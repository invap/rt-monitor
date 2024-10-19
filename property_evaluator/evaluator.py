# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging

from errors.errors import AbortRun
from property_evaluator.py_property_evaluator import PyPropertyEvaluator
from property_evaluator.smt2_property_evaluator import SMT2PropertyEvaluator
from property_evaluator.sympy_property_evaluator import SymPyPropertyEvaluator


class Evaluator:

    def __init__(self, components, process_state, execution_state, timed_state):
        self._smt2_evaluator = SMT2PropertyEvaluator(components, process_state, execution_state, timed_state)
        self._py_evaluator = PyPropertyEvaluator(components, process_state, execution_state, timed_state)
        self._sympy_evaluator = SymPyPropertyEvaluator(components, process_state, execution_state, timed_state)

    def eval(self, property, now):
        match property.format():
            case "protosmt2":
                return self._smt2_evaluator.eval(property, now)
            case "protopy":
                return self._py_evaluator.eval(property, now)
            case "protosympy":
                return self._sympy_evaluator.eval(property, now)
            case _:
                logging.error(f"Property format [ {property.format()} ] unknown.")
                raise AbortRun()
