import logging
import os

from workflow_runtime_verification.errors import NoValueAssignedToVariable, FormulaError, UnboundVariables
from workflow_runtime_verification.specification.Py_interpreted_property import PyInterpretedProperty
from workflow_runtime_verification.specification.logic_property import LogicProperty


class PyProperty(PyInterpretedProperty):
    def __init__(self, filename, variables, formula):
        super().__init__(filename, variables, formula)

    def eval_with(self, event_time, monitor):
        return monitor.eval_py(event_time,
                               monitor.py_build_spec(event_time, self),
                               self.filename())

    @staticmethod
    def _property_from_file(file_name, specification_file_directory):
        file_name_ext = file_name + ".protopy"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        variables, spec = LogicProperty.prespec_from_file(file_path)
        return PyProperty(variables, spec, file_name)

    def _build_spec(self, component_dictionary, timed_state, execution_state):
        try:
            assumptions = self._build_assumptions(component_dictionary, timed_state, execution_state)
            spec = (f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = not {self.formula()}\n")
            return spec
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.get_varnames()} ] has no value.")
            raise FormulaError(self.formula())
        except UnboundVariables as e:
            logging.error(f"Unbounded variables [ {e.get_varnames()} ] in formula [ {self.filename()} ]")
            raise FormulaError(self.formula())

