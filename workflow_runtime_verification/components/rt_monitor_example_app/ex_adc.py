import numpy as np

from workflow_runtime_verification.components.component import Component
from workflow_runtime_verification.components.rt_monitor_example_app import (
    ex_adcVisual,
)
from workflow_runtime_verification.errors import NoValue


class adc(Component):
    def __init__(self):
        super().__init__()
        self._adc_read = NoValue()

        self.__total_values_read = 0
        self.__current_value = 0
        self.__visualADC = ex_adcVisual.adcVisual(parent=self, adc_component=self)
        self.__visualADC.Show()

    def stop(self):
        self.__visualADC.close()

    def state(self):
        state = {"adc_read": [["uint16_t"], self._adc_read]}
        return state

    def exported_functions(self):
        return {"adc_init": self.adc_init, "sample": self.sample}

    def adc_init(self):
        pass

    def sample(self, read: np.uint16):
        self._adc_read = read
        self.__total_values_read += 1
        self.__current_value = read

    def get_status(self):
        return [self.__total_values_read, self.__current_value]
