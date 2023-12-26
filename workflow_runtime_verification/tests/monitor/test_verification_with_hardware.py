import wx

from workflow_runtime_verification.hardware_devices.c_example_app.ex_adc import adc
from workflow_runtime_verification.monitor import Monitor
from workflow_runtime_verification.tests.test import Test


class VerificationWithHardwareTest(Test):
    def test_verifies_a_valid_report_verifying_hardware_properties(self):
        _app = wx.App()
        workflow_specification = self.objects.workflow_specification_with_one_task()
        hardware_dictionary = {
            self._hardware_component_name(): self._hardware_component()
        }
        monitor = Monitor(workflow_specification, hardware_dictionary)
        event_report = [
            self.objects.hardware_encoded_event(
                self._hardware_component_name(), self._hardware_event_data()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def _hardware_component(self):
        return adc()

    def _hardware_component_name(self):
        return "adc"

    def _hardware_event_data(self):
        return "sample,2042"
