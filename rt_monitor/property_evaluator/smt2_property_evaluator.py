# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from typing import Iterable

import numpy as np
from z3 import z3

from errors.clock_errors import ClockWasNotStartedError
from errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError,
    UnsupportedSMT2VariableTypeError
)
from novalue import NoValue
from property_evaluator.property_evaluator import PropertyEvaluator


class SMT2PropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, property, now):
        spec = self._build_spec(property, now)
        filename = property.filename()
        temp_solver = z3.Solver()
        temp_solver.from_string(spec)
        negation_is_sat = z3.sat == temp_solver.check()
        if negation_is_sat:
            # Output counterexample as toml_tasks_list
            spec_filename = filename + "@" + str(now) + ".smt2"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_sat

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            declarations = self._build_declarations(prop)
            assumptions = self._build_assumptions(prop, now)
            spec = (f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"(assert (not {prop.formula()}))\n")
            return spec
        except UnsupportedSMT2VariableTypeError:
            pass
        except NoValueAssignedToVariableError:
            pass
        except UnboundVariablesError:
            pass
        except ClockWasNotStartedError():
            pass
        raise BuildSpecificationError()

    # Raises: UnsupportedSMT2VariableTypeError()
    @staticmethod
    def _build_declaration(variable, variable_type):
        match variable_type:
            case _:  # ToDo: characterize the correct array types: T = {Bool | Int | Real} + (Array Int T)
                return f"(declare-const {variable} {variable_type})"
            # case _:
            #     logging.error(f"Variable type [ {variable_type} ] of variable [ {variable} ] unsupported.")
            #     raise UnsupportedSMT2VariableTypeError()

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, Iterable):
            if any([isinstance(x, NoValue) for x in variable_value]):
                logging.error(f"No value [ {variable} ] has not been assigned a value.")
                raise NoValueAssignedToVariableError()
        elif isinstance(variable_value, NoValue):
            logging.error(f"No value [ {variable} ] has not been assigned a value.")
            raise NoValueAssignedToVariableError()
        # The variable has a value assigned.
        assumption = "(assert \n"
        if not isinstance(variable_value, np.ndarray):
            assumption = assumption + f"(= {variable} {variable_value})\n"
        else:
            assumption = assumption + "(and \n"
            var_value_shape = variable_value.shape
            current = [0] * (len(var_value_shape) + 1)
            while _more(current):
                value = _get_value(variable_value, current)
                selector = _build_selector(variable, current)
                assumption = assumption + f"(= {selector} {value})\n"
                _plus_one(var_value_shape, current)
            assumption = assumption + ")\n"
        assumption = assumption + ")"
        return assumption

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logging.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        assumption = f"(assert (= {variable} {clock.get_time(now)}))\n"
        return assumption


def _plus_one_in_position(shape_, current, position):
    if position == 0:
        current[position] = 1
    else:
        carry = 1
        while carry == 1 and position > 0:
            new_value = (current[position] + 1) % shape_[position - 1]
            carry = (current[position] + 1) // shape_[position - 1]
            current[position] = new_value
            if current[position] == 0:
                _plus_one_in_position(shape_, current, position - 1)
                carry = 0


def _plus_one(shape_, current):
    _plus_one_in_position(shape_, current, len(current) - 1)


def _more(current):
    return current[0] == 0


def _get_value(array_value, current):
    value = array_value
    for position in range(1, len(current)):
        value = value[current[position]]
    return value


def _build_selector(var_name, current):
    select = var_name
    for position in range(1, len(current)):
        select = f"(select {select} {current[position]})"
    return select
