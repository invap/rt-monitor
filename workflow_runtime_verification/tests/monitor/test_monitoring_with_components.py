import wx

from workflow_runtime_verification.components.rt_monitor_example_app.ex_adc import (
    adc,
)
from workflow_runtime_verification.monitor import Monitor
from workflow_runtime_verification.tests.test import Test


class MonitoringWithComponentsTest(Test):
    def test_verifies_a_valid_report_verifying_component_properties(self):
        self._initialize_app_for_visual_components()
        workflow_specification = self.objects.workflow_specification_with_one_task()
        component_dictionary = {self._component_name(): self._component()}
        monitor = Monitor(workflow_specification, component_dictionary)
        event_report = [
            self.objects.component_encoded_event(
                self._component_name(), self._component_event_data()
            ),
        ]

        is_report_valid = monitor.run(event_report)

        self.assertTrue(is_report_valid)

    def _initialize_app_for_visual_components(self):
        self._app = wx.App()

    def _component(self):
        return adc()

    def _component_name(self):
        return "adc"

    def _component_event_data(self):
        return "sample,2042"
