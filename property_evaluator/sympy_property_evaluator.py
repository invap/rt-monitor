# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from typing import Iterable

from process_rt_monitor.clock_errors import ClockWasNotStarted
from process_rt_monitor.errors import NoValueAssignedToVariable, FormulaError, UnboundVariables
from process_rt_monitor.process.novalue import NoValue
from process_rt_monitor.process.process_errors import UnsupportedSymPyVariableType
from property_evaluator.property_evaluator import PropertyEvaluator


class SymPyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    def eval(self, property, now):
        spec = self._build_spec(property, now)
        filename = property.filename()
        locs = {}
        exec(spec, globals(), locs)
        negation_is_true = locs['result']
        if negation_is_true:
            # Output counterexample as toml_tasks_list
            spec_filename = filename + "@" + str(now) + ".py"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_true

    def _build_spec(self, property, now):
        try:
            declarations = self._build_declarations(property)
            assumptions = self._build_assumptions(property, now)
            spec = (f"from sympy import Symbol\n" +
                    f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {property.formula()}\n")
            return spec
        except UnsupportedSymPyVariableType as e:
            logging.error(
                f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                f"{e.get_formula_type()} formula [ {property.filename()} ].")
            raise FormulaError(property.formula())
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ]  in formula [ {property.filename()} ] has no value.")
            raise FormulaError(property.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {property.filename()} ].")
            raise FormulaError(property.formula())

    @staticmethod
    def _build_declaration(variable, variable_type):
        match variable_type:
            case "Bool":
                return f"{variable} = Symbol('{variable}')"
            case "Int":
                return f"{variable} = Symbol('{variable}', integer=True)"
            case "Real":
                return f"{variable} = Symbol('{variable}', real=True)"
            case _:
                raise UnsupportedSymPyVariableType(variable, variable_type)

    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, Iterable):
            if any([isinstance(x, NoValue) for x in variable_value]):
                raise NoValueAssignedToVariable(variable)
        elif isinstance(variable_value, NoValue):
            raise NoValueAssignedToVariable(variable)
        # The variable has a value assigned.
        return f"{variable} = {variable_value}"

    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            raise ClockWasNotStarted(variable)
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"
