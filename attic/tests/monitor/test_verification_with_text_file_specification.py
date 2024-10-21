# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from errors.errors import AbortRun
from monitor import Monitor
from framework.process.process import (
    Process,
)
from attic.tests.test import Test


class VerificationWithTextFileSpecificationTest(Test):
    def test_verifies_a_valid_report_for_a_workflow_with_a_cycle_and_a_choice(self):
        monitor = self.objects.monitor_with_no_components_for(
            self._workflow_specification_from_file_with_cycle_inside_a_choice()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_when_a_started_tasks_preconditions_are_refuted(self):
        monitor = self.objects.monitor_with_no_components_for(
            self._workflow_specification_from_file_with_unsatisfied_precondition()
        )
        event_report = self.events_declaring_the_variables() + [
            self.objects.task_started_encoded_event(self.objects.task_name())
        ]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_refutes_a_report_when_a_finished_tasks_postconditions_are_refuted(self):
        monitor = self.objects.monitor_with_no_components_for(
            self._workflow_specification_from_file_with_unsatisfied_postcondition()
        )
        event_report = self.events_declaring_the_variables() + [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
        ]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_verifies_a_report_that_verifies_a_satisfied_global_checkpoint_property(
        self,
    ):
        monitor = Monitor(
            self._workflow_specification_with_global_checkpoint_from_file(),
            self.objects.empty_component_dictionary(),
        )
        event_report = self.events_declaring_the_variables() + [
            self.objects.variable_value_assigned_encoded_event(
                self.objects.variable_names(),
                self.objects.variable_value(),
            ),
            self.objects.variable_value_assigned_encoded_event(
                self.objects.another_variable_name(),
                self.objects.another_variable_value(),
            ),
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name(),
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_report_that_verifies_a_satisfied_local_checkpoint_property(
        self,
    ):
        monitor = Monitor(
            self._workflow_specification_with_local_checkpoints_from_file(),
            self.objects.empty_component_dictionary(),
        )
        event_report = self.events_declaring_the_variables() + [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.variable_value_assigned_encoded_event(
                self.objects.variable_names(),
                self.objects.variable_value(),
            ),
            self.objects.variable_value_assigned_encoded_event(
                self.objects.another_variable_name(),
                self.objects.another_variable_value(),
            ),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name(),
            ),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def _workflow_specification_from_file_with_cycle_inside_a_choice(self):
        workflow_specification_file_path = self._resource_path_for(
            "workflow_with_a_cycle_and_a_choice_specification.txt"
        )
        return Process.new_from_file(workflow_specification_file_path)

    def _workflow_specification_from_file_with_unsatisfied_precondition(self):
        workflow_specification_file_path = self._resource_path_for(
            "workflow_with_unsatisfied_precondition_specification.txt"
        )
        return Process.new_from_file(workflow_specification_file_path)

    def _workflow_specification_from_file_with_unsatisfied_postcondition(self):
        workflow_specification_file_path = self._resource_path_for(
            "workflow_with_unsatisfied_postcondition_specification.txt"
        )
        return Process.new_from_file(workflow_specification_file_path)

    def _workflow_specification_with_global_checkpoint_from_file(self):
        workflow_specification_file_path = self._resource_path_for(
            "workflow_with_global_checkpoint_specification.txt"
        )
        return Process.new_from_file(workflow_specification_file_path)

    def _workflow_specification_with_local_checkpoints_from_file(self):
        workflow_specification_file_path = self._resource_path_for(
            "workflow_with_local_checkpoints_specification.txt"
        )
        return Process.new_from_file(workflow_specification_file_path)

    def events_declaring_the_variables(self):
        return [
            self.objects.declared_variable_encoded_event(
                self.objects.variable_names(),
                self.objects.variable_type(),
            ),
            self.objects.declared_variable_encoded_event(
                self.objects.another_variable_name(),
                self.objects.variable_type(),
            ),
        ]

    def _expect_verification_to_be_aborted(self, event_report, monitor):
        self._expect_error_to_be_raised_when_verifying(AbortRun, event_report, monitor)

    def _expect_error_to_be_raised_when_verifying(
        self, error_type, event_report, monitor
    ):
        error_raised = False
        try:
            monitor.run(event_report)
        except error_type:
            error_raised = True
        self.assertTrue(error_raised)
