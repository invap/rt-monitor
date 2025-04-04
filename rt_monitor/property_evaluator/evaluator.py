# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging

from rt_monitor.errors.evaluator_errors import EvaluationError
from rt_monitor.property_evaluator.py_property_evaluator import PyPropertyEvaluator
from rt_monitor.property_evaluator.smt2_property_evaluator import SMT2PropertyEvaluator
from rt_monitor.property_evaluator.sympy_property_evaluator import SymPyPropertyEvaluator


class Evaluator:
    def __init__(self, components, process_state, execution_state, timed_state):
        self._smt2_evaluator = SMT2PropertyEvaluator(components, process_state, execution_state, timed_state)
        self._py_evaluator = PyPropertyEvaluator(components, process_state, execution_state, timed_state)
        self._sympy_evaluator = SymPyPropertyEvaluator(components, process_state, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, prop, now):
        match prop.format():
            case "smt2":
                return self._smt2_evaluator.eval(prop, now)
            case "py":
                return self._py_evaluator.eval(prop, now)
            case "sympy":
                return self._sympy_evaluator.eval(prop, now)
            case _:
                logging.error(f"Property format [ {prop.format()} ] unknown.")
                raise EvaluationError()
