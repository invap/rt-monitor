import unittest

from attic.logic_property import LogicProperty
from workflow_runtime_verification.specification.workflow_node.task_specification import (
    TaskSpecification,
)
from workflow_runtime_verification.tests.test import Test


class Z3TaskPropertiesVerificationTest(Test):
    @unittest.skip("Overlapped by broader tests.")
    def test_verifies_a_state_matching_an_smt2_property(self):
        task_specification = self._task_specification_with_smt2_specified_precondition()

        is_state_valid = task_specification.verify_precondition(
            self._state_matching_smt2_specified_property()
        )

        self.assertTrue(is_state_valid)

    @unittest.skip("Overlapped by broader tests.")
    def test_refutes_a_state_not_matching_an_smt2_property(self):
        task_specification = self._task_specification_with_smt2_specified_precondition()

        is_state_valid = task_specification.verify_precondition(
            self._state_not_matching_smt2_specified_property()
        )

        self.assertFalse(is_state_valid)

    @unittest.skip("Overlapped by broader tests.")
    def test_refutes_a_state_missing_variables_needed_by_an_smt2_property(self):
        task_specification = self._task_specification_with_smt2_specified_precondition()

        is_state_valid = task_specification.verify_precondition(
            self.objects.empty_execution_state()
        )

        self.assertFalse(is_state_valid)

    def _task_specification_with_smt2_specified_precondition(self):
        return TaskSpecification(
            self.objects.task_name(), preconditions={self._smt2_written_property()}
        )

    def _smt2_written_property(self):
        smt2_specification_file_path = self._resource_path_for("property.protosmt2")
        return LogicProperty.from_smt2_specification(smt2_specification_file_path)

    def _state_matching_smt2_specified_property(self):
        return {
            self._smt2_variable_name(): self.objects.variable_value(),
            self._another_smt2_variable_name(): self.objects.another_variable_value(),
        }

    def _state_not_matching_smt2_specified_property(self):
        return {
            self._smt2_variable_name(): "unexpected value",
            self._another_smt2_variable_name(): "unexpected value",
        }

    def _smt2_variable_name(self):
        return "variable"

    def _another_smt2_variable_name(self):
        return "another_variable"