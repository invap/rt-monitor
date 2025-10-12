import io
import os
import sys

from workflow_runtime_verification.tests.test import Test


class EventNotificationOutputTest(Test):
    def test_outputs_events_to_standard_output(self):
        output_buffer = self._buffer_capturing_standard_output()
        event_reporter = self.objects.event_reporter_with_output(sys.stdout)

        serialized_event = event_reporter.report_task_started(
            self.objects.task_name(), self.objects.time()
        )

        line_read_from_standard_output = self._read_last_line_from_stream(output_buffer)
        self.assertEqual(serialized_event, line_read_from_standard_output)
        self._restore_standard_output()

    def test_outputs_events_to_file(self):
        report_file_name = "test_report_output_file.txt"
        with open(report_file_name, "w+") as report_file:
            event_reporter = self.objects.event_reporter_with_output(report_file)

            serialized_event = event_reporter.report_task_started(
                self.objects.task_name(), self.objects.time()
            )

            line_read_from_standard_output = self._read_last_line_from_file(report_file)
            self.assertEqual(serialized_event + "\n", line_read_from_standard_output)
            self._restore_standard_output()

        os.remove(report_file_name)

    @staticmethod
    def _buffer_capturing_standard_output():
        buffer = io.StringIO()
        sys.stdout = buffer
        return buffer

    @staticmethod
    def _restore_standard_output():
        sys.stdout = sys.__stdout__

    @staticmethod
    def _read_last_line_from_stream(output_buffer):
        lines = output_buffer.getvalue().splitlines()
        return lines[-1] if lines else None

    @staticmethod
    def _read_last_line_from_file(report_file):
        report_file.seek(0)
        lines = report_file.readlines()
        return lines[-1]
