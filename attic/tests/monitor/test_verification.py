# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import unittest

from errors.errors import AbortRun
from reporting.event_decoder import InvalidEvent
from framework.process.process_node.checkpoint import (
    Checkpoint,
)
from attic.tests.test import Test


class VerificationTest(Test):
    def test_verifies_a_report_without_task_events_against_any_specification(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        is_report_valid = monitor.run(self.objects.report_without_task_events())

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_when_an_event_type_could_not_be_decoded(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = [self.objects.encoded_event_with_invalid_type()]

        self._expect_invalid_event_to_be_detected_when_verifying(event_report, monitor)

    def test_refutes_a_report_when_an_event_has_no_parameters(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = [self.objects.encoded_event_with_no_parameters()]

        self._expect_invalid_event_to_be_detected_when_verifying(event_report, monitor)

    def test_refutes_a_report_when_an_events_time_delimiter_is_missing(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = [self.objects.encoded_event_without_time_delimiter()]

        self._expect_invalid_event_to_be_detected_when_verifying(event_report, monitor)

    def test_raises_an_error_when_a_value_assignment_is_missing_value_delimiter(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = [self.objects.value_assignment_event_without_value_delimiter()]

        self._expect_invalid_event_to_be_detected_when_verifying(event_report, monitor)

    def test_verifies_a_valid_report_for_a_started_task(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = self.objects.event_report_with_many_variables()
        event_report.append(
            self.objects.task_started_encoded_event(self.objects.task_name())
        )

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_valid_report_for_a_finished_task(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = self.objects.event_report_with_many_variables()
        event_report.append(
            self.objects.task_started_encoded_event(self.objects.task_name())
        )
        event_report.append(
            self.objects.task_finished_encoded_event(self.objects.task_name())
        )

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_that_verifies_a_non_existent_checkpoint(self):
        monitor = self.objects.monitor_for_workflow_with_one_task()
        event_report = [
            self.objects.checkpoint_reached_encoded_event(
                self.objects.non_existent_checkpoint_name()
            )
        ]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_refutes_a_report_that_verifies_an_unsatisfied_checkpoint_property(self):
        checkpoint = Checkpoint(
            self.objects.checkpoint_name(), {self.objects.unsatisfied_property()}
        )
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_before_checkpoint(
                checkpoint
            )
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_report_that_verifies_a_satisfied_checkpoint_property(self):
        checkpoint = Checkpoint(
            self.objects.checkpoint_name(), {self.objects.satisfied_property()}
        )
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_before_checkpoint(
                checkpoint
            )
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_satisfied_local_checkpoint_property(self):
        checkpoint = Checkpoint(
            self.objects.checkpoint_name(), {self.objects.satisfied_property()}
        )
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_and_local_checkpoint(
                checkpoint
            )
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name()
            ),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_the_repetition_of_a_local_checkpoint(self):
        checkpoint = Checkpoint(
            self.objects.checkpoint_name(), {self.objects.satisfied_property()}
        )
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_and_local_checkpoint(
                checkpoint
            )
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name()
            ),
            self.objects.checkpoint_reached_encoded_event(
                self.objects.checkpoint_name()
            ),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_that_verifies_using_a_non_existent_variable(self):
        checkpoint_name = "prop with non-existent variable"
        checkpoint = Checkpoint(
            checkpoint_name, {self.objects.property_with_non_existent_variable()}
        )
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_before_checkpoint(
                checkpoint
            )
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.task_name()),
            self.objects.task_finished_encoded_event(self.objects.task_name()),
            self.objects.checkpoint_reached_encoded_event(checkpoint_name),
        ]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_verifies_required_tasks_of_a_starting_task(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_many_tasks()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_report_when_all_required_tasks_are_executed(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_many_tasks()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_report_when_a_started_task_has_no_preconditions(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_without_conditions()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_without_conditions_name()
            )
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_when_a_started_tasks_preconditions_are_refuted(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_task_with_unsatisfied_precondition()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_with_unsatisfied_precondition_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_report_when_a_started_tasks_preconditions_are_met(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_task_with_satisfied_precondition()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_with_satisfied_precondition_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_report_when_a_started_task_has_no_postconditions(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task_without_conditions()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_without_conditions_name()
            ),
            self.objects.task_finished_encoded_event(
                self.objects.task_without_conditions_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_report_when_a_started_tasks_postconditions_are_met(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_task_with_satisfied_postcondition()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_with_satisfied_postcondition_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_when_a_finished_tasks_postconditions_are_refuted(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_task_with_unsatisfied_postcondition()
        )
        event_report = [
            self.objects.task_started_encoded_event(
                self.objects.task_with_unsatisfied_postcondition_name()
            ),
            self.objects.task_finished_encoded_event(
                self.objects.task_with_unsatisfied_postcondition_name()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_a_finished_task_without_a_start_event_for_it(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task()
        )
        event_report = [
            self.objects.task_finished_encoded_event(self.objects.task_name())
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_a_started_non_existent_task(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_one_task()
        )
        event_report = [self.objects.task_started_encoded_event("non-existent task")]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_refutes_a_report_with_a_finished_non_existent_task(self):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_choice()
        event_report = [self.objects.task_finished_encoded_event("non-existent task")]

        self._expect_verification_to_be_aborted(event_report, monitor)

    def test_refutes_a_report_with_more_than_one_choice_task_executed(self):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_choice()
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_more_than_one_choice_task_executed_with_cycle(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle_inside_a_choice()
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
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_more_than_one_choice_task_executed_with_fork(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_parallel_nested_in_choice()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_report_with_exactly_one_choice_task_executed(self):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_choice()
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_when_a_task_is_executed_before_its_required_task_choice(
        self,
    ):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_choice()
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_when_a_task_choice_is_executed_before_its_required_tasks(
        self,
    ):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_choice()
        event_report = [
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_valid_report_for_a_workflow_ending_in_a_choice(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_ending_in_choice()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_repeating_a_task_outside_a_cycle(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_many_tasks()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_valid_report_with_repetition_for_a_workflow_with_a_cycle(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_refutes_a_report_with_a_repetition_of_an_unfinished_cycle(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_a_cycle_not_starting_from_the_cycle_start(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_a_repetition_after_the_cycle_ends(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_refutes_a_report_with_continuation_after_a_partially_looped_cycle(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_cycle()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def test_verifies_a_valid_report_for_a_workflow_with_nested_cycles_without_overlap(
        self,
    ):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_nested_cycles()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def test_verifies_a_report_which_cycles_over_a_complete_workflow(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_many_tasks()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    # Parallel tests

    @unittest.skip("Parallel tasks are not supported")
    def test_verifies_a_valid_report_for_a_composition_nested_in_a_choice(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_parallel_nested_in_choice()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    @unittest.skip("Parallel tasks are not supported")
    def test_verifies_a_valid_report_for_a_composition_nested_in_a_parallel(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_choice_nested_in_parallel()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    @unittest.skip("Parallel tasks are not supported")
    def test_verifies_a_valid_report_for_a_workflow_ending_in_a_parallel(self):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_ending_in_parallel()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    @unittest.skip("Parallel tasks are not supported")
    def test_verifies_a_valid_report_for_a_parallel_nested_in_a_choice_not_executing_the_parallel_branch(
        self,
    ):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_parallel_nested_in_choice()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    @unittest.skip("Parallel tasks are not supported")
    def test_refutes_a_report_with_more_than_one_choice_task_executed_inside_parallel(
        self,
    ):
        monitor = self.objects.monitor_with_no_components_for(
            self.objects.workflow_specification_with_choice_nested_in_parallel()
        )
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_2_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_3_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
            self.objects.task_finished_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    @unittest.skip("Parallel tasks are not supported")
    def test_refutes_a_report_when_a_task_is_executed_before_its_required_task_parallel(
        self,
    ):
        monitor = self.objects.monitor_for_workflow_with_many_tasks_and_parallel()
        event_report = [
            self.objects.task_started_encoded_event(self.objects.starting_task_name()),
            self.objects.task_finished_encoded_event(self.objects.starting_task_name()),
            self.objects.task_started_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_finished_encoded_event(self.objects.middle_task_1_name()),
            self.objects.task_started_encoded_event(self.objects.final_task_name()),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertFalse(is_report_valid)

    def _expect_invalid_event_to_be_detected_when_verifying(
        self, event_report, monitor
    ):
        self._expect_error_to_be_raised_when_verifying(
            InvalidEvent, event_report, monitor
        )

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
