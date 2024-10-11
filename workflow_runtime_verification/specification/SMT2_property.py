import logging
import os
from collections.abc import Iterable

import numpy as np
import z3

from workflow_runtime_verification.errors import NoValueAssignedToVariable, UnboundVariables, FormulaError, NoValue, \
    UnsupportedSMT2VariableType
from workflow_runtime_verification.specification.logic_property import LogicProperty


class SMT2Property(LogicProperty):
    def __init__(self, variables, formula, filename):
        super().__init__(variables, formula, filename)

    @staticmethod
    def property_from_file(file_name, specification_file_directory):
        file_name_ext = file_name + ".protosmt2"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        variables, formula = LogicProperty.prespec_from_file(file_path)
        return SMT2Property(variables, formula, file_name)

    def eval(self, event_time, component_dictionary, timed_state, execution_state):
        spec = self._build_spec(component_dictionary, timed_state, execution_state)
        filename = self.filename()
        temp_solver = z3.Solver()
        temp_solver.from_string(spec)
        negation_is_sat = z3.sat == temp_solver.check()
        if negation_is_sat:
            # Output counterexample as specification
            spec_filename = filename + "@" + str(event_time) + ".smt2"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_sat

    def _build_spec(self, component_dictionary, timed_state, execution_state):
        try:
            declarations = self._build_declarations(component_dictionary, timed_state, execution_state)
            assumptions = self._build_assumptions(component_dictionary, timed_state, execution_state)
            spec = (f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"(assert (not {self.formula()}))\n")
            return spec
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ]")
            raise FormulaError(self.formula())

    def _build_declarations(self, component_dictionary, timed_state, execution_state):
        declarations = []
        variables = list((self.variables()).keys())
        for varname in execution_state:
            if varname in variables:
                if isinstance(execution_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                declarations.append(f"(declare-const {varname} {self.variables()[varname]})")
                variables.remove(varname)
        for component in component_dictionary:
            dictionary = component_dictionary[component].state()
            for varname in dictionary:
                if varname in variables:
                    # The value of the variable of the state might be iterable.
                    if isinstance(dictionary[varname][1], Iterable):
                        if any([isinstance(x, NoValue) for x in dictionary[varname][1]]):
                            raise NoValueAssignedToVariable(varname)
                    elif isinstance(dictionary[varname][1], NoValue):
                        raise NoValueAssignedToVariable(varname)
                    declarations.append(f"(declare-const {varname} {self.variables()[varname]})")
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return declarations

    def _build_assumptions(self, component_dictionary, timed_state, execution_state):
        assumptions = []
        # Building a set from the frozen set containing the variables occurring in the formula
        variables = list((self.variables()).keys())
        for varname in execution_state:
            if varname in variables:
                if isinstance(execution_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                try:
                    assumptions.append(_build_assumption(
                        varname, execution_state[varname][1]
                    ))
                except UnsupportedSMT2VariableType as e:
                    logging.error(
                        f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                        f"{e.get_formula_type()} formula [ {self.filename()} ]")
                    raise FormulaError(self.formula())
                variables.remove(varname)
        for device in component_dictionary:
            dictionary = component_dictionary[device].state()
            for varname in dictionary:
                if varname in variables:
                    # The value of the variable of the state might be iterable.
                    if isinstance(dictionary[varname][1], Iterable):
                        if any([isinstance(x, NoValue) for x in dictionary[varname][1]]):
                            raise NoValueAssignedToVariable(varname)
                    elif isinstance(dictionary[varname][1], NoValue):
                        raise NoValueAssignedToVariable(varname)
                    try:
                        assumptions.append(_build_assumption(
                            varname, dictionary[varname][1]
                        ))
                    except UnsupportedSMT2VariableType as e:
                        logging.error(
                            f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                            f"{e.get_formula_type()} formula [ {self.filename()} ]")
                        raise FormulaError(self.formula())
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return assumptions


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


def _build_assumption(var_name, var_value):
    assumption = "(assert \n"
    if not isinstance(var_value, np.ndarray):
        assumption = assumption + f"(= {var_name} {var_value})\n"
    else:
        assumption = assumption + "(and \n"
        var_value_shape = var_value.shape
        current = [0] * (len(var_value_shape) + 1)
        while _more(current):
            value = _get_value(var_value, current)
            selector = _build_selector(var_name, current)
            assumption = assumption + f"(= {selector} {value})\n"
            _plus_one(var_value_shape, current)
        assumption = assumption + ")\n"
    assumption = assumption + ")"
    return assumption
