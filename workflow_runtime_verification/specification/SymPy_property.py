import logging
import os
from collections.abc import Iterable

from workflow_runtime_verification.errors import (
    NoValueAssignedToVariable,
    UnboundVariables,
    FormulaError,
    NoValue,
    ClockWasNotStarted
)
from workflow_runtime_verification.specification.Py_interpreted_property import PyInterpretedProperty
from workflow_runtime_verification.specification.logic_property import LogicProperty
from workflow_runtime_verification.specification.specification_errors import UnsupportedSymPyVariableType


class SymPyProperty(PyInterpretedProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    @staticmethod
    def property_from_file(file_name, specification_file_directory):
        file_name_ext = file_name + ".protosympy"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        variables, formula = LogicProperty.prespec_from_file(file_path)
        return SymPyProperty(variables, formula, file_name)

    def _build_spec(self, component_dictionary, timed_state, execution_state):
        try:
            declarations = self._build_declarations(component_dictionary, timed_state, execution_state)
            assumptions = self._build_assumptions(component_dictionary, timed_state, execution_state)
            spec = (f"from sympy import Symbol\n" +
                    f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {self.formula()}\n")
            return spec
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ]")
            raise FormulaError(self.formula())

    def _build_declarations(self, component_dictionary, timed_state, execution_state, now):
        declarations = []
        # Building a set from the frozen set containing the variables occurring in the formula
        variables = (self.variables()).keys()
        for variable in timed_state:
            if variable in variables:
                if isinstance(timed_state[variable].get_time(now), NoValue):
                    raise ClockWasNotStarted(variable)
                declarations.append(f"{variable} = Symbol('{variable}', integer=True, positive=True)")
                variables.remove(variable)
        for varname in execution_state:
            if varname in variables:
                if isinstance(execution_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                try:
                    declarations.append(
                        f"{self._sympy_hostlanguage_type_2_sympy_type(varname, execution_state[varname][0])}")
                except UnsupportedSymPyVariableType as e:
                    logging.error(
                        f'Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in '
                        f'{e.get_formula_type()} formula [ {self.filename()} ]')
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
                        declarations.append(
                            f"{self._sympy_hostlanguage_type_2_sympy_type(varname, dictionary[varname][0])}")
                    except UnsupportedSymPyVariableType as e:
                        logging.error(
                            f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                            f"{e.get_formula_type()} formula [ {self.filename()} ]")
                        raise FormulaError(self.formula())
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return declarations

    @staticmethod
    def _sympy_hostlanguage_type_2_sympy_type(varname, var_hostlanguage_type):
        match var_hostlanguage_type[0]:
            # C supported types
            case "bool":
                return f"{varname} = Symbol('{varname}')"  # {true, false}}
            case "char_t":
                return f"{varname} = Symbol('{varname}', integer=True, positive=True)"  # -128 <= varname < 128
            case "uint8_t":
                return f"{varname} = Symbol('{varname}', integer=True, positive=True)"  # 0 <= varname < 255
            case "int8_t":
                return f"{varname} = Symbol('{varname}', integer=True)"  # -128 <= varname < 128
            case "uint16_t":
                return f"{varname} = Symbol('{varname}', integer=True, positive=True)\n"  # 0 <= varname < 65535
            case "int16_t":
                return f"{varname} = Symbol('{varname}', integer=True)"  # -32768 <= varname < 32768
            case "int":
                return f"{varname} = Symbol('{varname}', integer=True)"  # -32768 <= varname < 32768
            case "unsigned int":
                return f"{varname} = Symbol('{varname}', integer=True, positive=True)"  # 0 <= varname < 65535
            case "float":
                return f"{varname} = Symbol('{varname}', real=True)"  # 1.175494351*10^(-38) <= varname <= 3.402823466*10^38
            case "double":
                return f"{varname} = Symbol('{varname}', real=True)"  # 2.2250738585072014*10^(-308) <= varname <= 1.7976931348623158*10^308
            case _:
                raise UnsupportedSymPyVariableType(varname, var_hostlanguage_type[0])

