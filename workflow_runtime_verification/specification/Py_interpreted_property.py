import logging
from collections.abc import Iterable

from workflow_runtime_verification.errors import NoValue, NoValueAssignedToVariable, ClockWasNotStarted, \
    UnsupportedPyVariableType, FormulaError, UnboundVariables, UnsupportedSymPyVariableType
from workflow_runtime_verification.specification.logic_property import LogicProperty


class PyInterpretedProperty(LogicProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    def eval(self, event_time, component_dictionary, timed_state, execution_state):
        spec = self._build_spec(component_dictionary, timed_state, execution_state)
        filename = self.filename()
        locs = {}
        exec(spec, globals(), locs)
        negation_is_true = locs['result']
        if negation_is_true:
            # Output counterexample as specification
            spec_filename = filename + "@" + str(event_time) + ".py"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logging.info(f"Specification dumped: [ {spec_filename} ]")
        return negation_is_true

    def _build_spec(self, component_dictionary, timed_state, execution_state):
        raise NotImplementedError

    def _build_assumptions(self, component_dictionary, timed_state, execution_state, now):
        assumptions = []
        # Building a set from the frozen set containing the variables occurring in the formula
        variables = set()
        for var in self.variables():
            variables.add(var)
        for clock_name in timed_state:
            if clock_name in variables:
                if isinstance(timed_state[clock_name].get_time(now), NoValue):
                    raise ClockWasNotStarted(clock_name)
                assumptions.append(f"{clock_name} = {timed_state[clock_name].get_time(now)}")
                variables.remove(clock_name)
        for varname in execution_state:
            if varname in variables:
                if isinstance(execution_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                assumptions.append(f"{varname} = {execution_state[varname][1]}")
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
                        assumptions.append(
                            self._build_assumption(varname, component_dictionary[device][varname][0],
                                                   component_dictionary[device][varname][1]))
                    except UnsupportedPyVariableType as e:
                        logging.error(
                            f"Unsupported variable type error [ {e.get_variable_name()}: {e.get_variable_type()} ] in "
                            f"{e.get_formula_type()} formula [ {self.filename()} ]")
                        raise FormulaError(self.formula())
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return assumptions

    @staticmethod
    def _build_assumption(varname, vartype, varvalue):
        match vartype:
            # C supported types
            case "bool":
                return f"{varname} = {varvalue}"
            case "char_t":
                return f"{varname} = {varvalue}"
            case "uint8_t":
                return f"{varname} = {varvalue}"
            case "int8_t":
                return f"{varname} = {varvalue}"
            case "uint16_t":
                return f"{varname} = {varvalue}"
            case "int16_t":
                return f"{varname} = {varvalue}"
            case "int":
                return f"{varname} = {varvalue}"
            case "unsigned int":
                return f"{varname} = {varvalue}"
            case "float":
                return f"{varname} = {varvalue}"
            case "double":
                return f"{varname} = {varvalue}"
            case _:
                raise UnsupportedSymPyVariableType(varname, vartype)
