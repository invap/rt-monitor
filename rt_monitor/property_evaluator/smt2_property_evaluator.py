# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging
import numpy as np
from z3 import z3

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError,
)
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


class SMT2PropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, process_state, execution_state, timed_state):
        super().__init__(components, process_state, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, property, now):
        spec = self._build_spec(property, now)
        filename = property.name()
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
            var_declarations = self._build_variable_declarations(prop)
            assumptions = self._build_assumptions(prop, now)
            spec = (f"{"".join([decl + "\n" for decl in var_declarations])}\n" +
                    f"{prop.declarations()}\n\n"
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"(assert (not {prop.formula()}))\n")
            return spec
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
        # As types are declared in the input files using SMT2Lib standard there is nothing to do here
        return f"(declare-const {variable} {variable_type})"

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        if isinstance(variable_value, np.ndarray):
            # The variable is of type np.ndarray, mainly used for implementing the internal structure
            # of digital twins
            if any([isinstance(x, NoValue) for x in variable_value]):
                logging.error(f"The variable [ {variable} ] has a member that has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
                # The instance has assigned values to all its components
                assumption = "(assert (and \n"
                var_value_shape = variable_value.shape
                current = [0] * (len(var_value_shape) + 1)
                while SMT2PropertyEvaluator._more(current):
                    value = SMT2PropertyEvaluator._get_value(variable_value, current)
                    selector = SMT2PropertyEvaluator._build_selector(variable, current)
                    assumption += f"(= {selector} {value})\n"
                    SMT2PropertyEvaluator._plus_one(var_value_shape, current)
                assumption += "))"
                return assumption
        elif isinstance(variable_value, dict):
            # The variable is of type dict, used for monitoring arrays whose dimension is unknown by the monitor
            if any([isinstance(x, NoValue) for x in variable_value.values()]):
                logging.error(f"The variable [ {variable} ] has a member that has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
                # The instance has assigned values to all its components
                assumption = "(assert \n"
                assumption += "(and \n"
                for key in variable_value:
                    # key if of the form [i0][i1]...[in]
                    split_key = key.removeprefix("[").removesuffix("]").split("][")
                    assumption += "(= "
                    for _i in range(0, len(split_key)):
                        assumption += f"(select "
                    assumption += f"{variable} "
                    for i in split_key:
                        assumption += f"{i}) "
                    assumption += f"{variable_value[key]})\n"
                assumption += ")\n)\n"
                return assumption
        else:
            # The variable is of one of the basic types supported expressed with a string
            if isinstance(variable_value, NoValue):
                logging.error(f"The variable [ {variable} ] has not been assigned a value.")
                raise NoValueAssignedToVariableError()
            else:
                assumption = f"(assert (= {variable} {variable_value}))\n"
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

    @staticmethod
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
                    SMT2PropertyEvaluator._plus_one_in_position(shape_, current, position - 1)
                    carry = 0

    @staticmethod
    def _plus_one(shape_, current):
        SMT2PropertyEvaluator._plus_one_in_position(shape_, current, len(current) - 1)

    @staticmethod
    def _more(current):
        return current[0] == 0

    @staticmethod
    def _get_value(array_value, current):
        value = array_value
        for position in range(1, len(current)):
            value = value[current[position]]
        return value

    @staticmethod
    def _build_selector(var_name, current):
        select = var_name
        for position in range(1, len(current)):
            select = f"(select {select} {current[position]})"
        return select
