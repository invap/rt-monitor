# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError,
    EvaluationError, UnsupportedSymPyVariableTypeError
)
from rt_monitor.logging_configuration import LoggingLevel
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


class SymPyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, now, prop):
        logging.log(LoggingLevel.ANALYSIS, f"Checking property {prop.name()}...")
        try:
            spec = self._build_spec(prop, now)
        except BuildSpecificationError:
            logging.error(f"Building specification for property [ {prop.name()} ] error.")
            raise EvaluationError()
        locs = {}
        # The formula is checked to be either true or false
        exec(spec, globals(), locs)
        result = locs['result']
        match result:
            case True:
                # If the formula is true, then the property of interest passed.
                logging.log(LoggingLevel.ANALYSIS, f"Property {prop.name()} PASSED")
            case False:
                # If the formula is false, then the property of interest failed.
                logging.log(LoggingLevel.ANALYSIS, f"Property {prop.name()} FAILED")
        if result == False:
            # Output counterexample as python program
            spec_filename = prop.name() + "@" + str(now) + ".py"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
            return PropertyEvaluator.PropertyEvaluationResult.FAILED
        else:
            return PropertyEvaluator.PropertyEvaluationResult.PASSED

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            declarations = self._build_variable_declarations(prop)
            assumptions = self._build_assumptions(prop, now)
            spec = (f"from sympy import Symbol\n" +
                    f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{prop.declarations()}\n\n"
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = {prop.formula()}\n")
            return spec
        except NoValueAssignedToVariableError:
            pass
        except UnboundVariablesError:
            pass
        except ClockWasNotStartedError:
            pass
        raise BuildSpecificationError()

    # Raises: UnsupportedSymPyVariableType()
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
                logging.error(f"Variable type [ {variable_type} ] of variable [ {variable} ] unsupported.")
                raise UnsupportedSymPyVariableTypeError()

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, NoValue):
            logging.error(f"The variable [ {variable} ] has not been assigned a value.")
            raise NoValueAssignedToVariableError()
        # The variable has a value assigned.
        return f"{variable} = {variable_value}"

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logging.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"
