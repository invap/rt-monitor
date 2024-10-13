# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import os
from collections.abc import Iterable

import numpy as np
import z3

from workflow_runtime_verification.clock_errors import ClockWasNotStarted
from workflow_runtime_verification.errors import (
    NoValueAssignedToVariable,
    UnboundVariables,
    FormulaError
)
from workflow_runtime_verification.specification.logic_property import LogicProperty
from workflow_runtime_verification.specification.novalue import NoValue
from workflow_runtime_verification.specification.specification_errors import UnsupportedSMT2VariableType


class SMT2Property(LogicProperty):
    def __init__(self, variables, formula, filename):
        super().__init__(variables, formula, filename)

    @staticmethod
    def property_from_file(file_name, specification_file_directory):
        file_name_ext = file_name + ".protosmt2"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        variables, formula = LogicProperty.prespec_from_file(file_path)
        return SMT2Property(variables, formula, file_name)

    def eval(self, component_dictionary, execution_state, timed_state, now):
        spec = self._build_spec(component_dictionary, execution_state, timed_state, now)
        filename = self.filename()
        temp_solver = z3.Solver()
        temp_solver.from_string(spec)
        negation_is_sat = z3.sat == temp_solver.check()
        if negation_is_sat:
            # Output counterexample as specification
            spec_filename = filename + "@" + str(now) + ".smt2"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_sat

    def _build_spec(self, component_dictionary, execution_state, timed_state, now):
        try:
            declarations = self._build_declarations(component_dictionary, execution_state, timed_state)
            assumptions = self._build_assumptions(component_dictionary, execution_state, timed_state, now)
            spec = (f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"(assert (not {self.formula()}))\n")
            return spec
        except UnsupportedSMT2VariableType as e:
            logging.error(
                f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                f"{e.get_formula_type()} formula [ {self.filename()} ].")
            raise FormulaError(self.formula())
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ]  in formula [ {self.filename()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ].")
            raise FormulaError(self.formula())

    @staticmethod
    def _build_declaration(variable, variable_type):
        match variable_type:
            case _:  # ToDo: characterize the correct array types: T = {Bool | Int | Real} + (Array Int T)
                return f"(declare-const {variable} {variable_type})"
            # case _:
            #     raise UnsupportedSymPyVariableType(variable, variable_type)

    @staticmethod
    def _build_assumption(variable, variable_value):
        # Check whether the variable has a value assigned.
        if isinstance(variable_value, Iterable):
            if any([isinstance(x, NoValue) for x in variable_value]):
                raise NoValueAssignedToVariable(variable)
        elif isinstance(variable_value, NoValue):
            raise NoValueAssignedToVariable(variable)
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

    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            raise ClockWasNotStarted(variable)
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


