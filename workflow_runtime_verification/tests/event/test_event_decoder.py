from workflow_runtime_verification.reporting.event.checkpoint_reached_event import (
    CheckpointReachedEvent,
)
from workflow_runtime_verification.reporting.event.task_finished_event import (
    TaskFinishedEvent,
)
from workflow_runtime_verification.reporting.event.task_started_event import (
    TaskStartedEvent,
)
from workflow_runtime_verification.reporting.event.variable_value_assigned_event import (
    VariableValueAssignedEvent,
)
from workflow_runtime_verification.reporting.event_decoder import EventDecoder
from workflow_runtime_verification.tests.test import Test


class EventDecoderTest(Test):
    def set_up(self):
        super().set_up()
        self._event_decoder = EventDecoder()
        self._event_reporter = self.objects.event_reporter()

    def test_decodes_the_start_of_a_task(self):
        serialized_event = self._event_reporter.report_task_started(
            self.objects.task_name(), self.objects.time()
        )

        event = self._event_decoder.decode(serialized_event)

        self.assertIsInstance(event, TaskStartedEvent)
        self.assertEqual(self.objects.task_name(), event.name())
        self.assertEqual(self.objects.time(), event.time())

    def test_decodes_the_end_of_a_task(self):
        serialized_event = self._event_reporter.report_task_finished(
            self.objects.task_name(), self.objects.time()
        )

        event = self._event_decoder.decode(serialized_event)

        self.assertIsInstance(event, TaskFinishedEvent)
        self.assertEqual(self.objects.task_name(), event.name())
        self.assertEqual(self.objects.time(), event.time())

    def test_decodes_the_assignment_of_a_variable_value(self):
        serialized_event = self._event_reporter.report_variable_value_assigned(
            self.objects.variable_name(),
            self.objects.variable_value(),
            self.objects.time(),
        )

        event = self._event_decoder.decode(serialized_event)

        self.assertIsInstance(event, VariableValueAssignedEvent)
        self.assertEqual(self.objects.variable_name(), event.variable_name())
        self.assertEqual(
            int(self.objects.variable_value()), int(event.variable_value())
        )
        self.assertEqual(self.objects.time(), event.time())

    def test_decodes_the_request_for_a_reached_checkpoint(self):
        serialized_event = self._event_reporter.report_checkpoint_reached(
            self.objects.checkpoint_name(),
            self.objects.time(),
        )

        event = self._event_decoder.decode(serialized_event)

        self.assertIsInstance(event, CheckpointReachedEvent)
        self.assertEqual(self.objects.checkpoint_name(), event.name())
        self.assertEqual(self.objects.time(), event.time())