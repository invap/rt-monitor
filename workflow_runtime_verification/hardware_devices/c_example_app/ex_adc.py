import inspect

import numpy as np

from workflow_runtime_verification.hardware_devices.c_example_app.ex_adcVisual import (
    adcVisual,
)
from workflow_runtime_verification.monitor import NoValue, FunctionNotImplemented


class adc:
    def __init__(self):
        AcumCalib = 0
        Calib = 0
        ContCalib = 0
        self._adc_read = NoValue()

        # statistics variables
        self.__total_values_read = 0
        self.__current_value = 0
        # create the visualization features associated
        self.__visualADC = adcVisual(parent=self, adc_comp=self)
        self.__visualADC.Show()

    def stop(self):
        self.__visualADC.close()

    def state(self):
        state = {"adc_read": [["uint16_t"], self._adc_read]}
        return state

    def adc_init(self):
        pass

    def sample(self, read: np.uint16):
        self._adc_read = read
        self.__total_values_read += 1
        self.__current_value = read

    def get_status(self):
        return [self.__total_values_read, self.__current_value]

    # component exported methods
    exported_functions = {"adc_init": adc_init, "sample": sample}

    def process_high_level_call(self, string_call):
        """
        This method receive as parameter a string_call containing a sequence of values,
        the first one is the class method name (e.g. lectura), then a lists of
        parameters for its call.
        """
        # get information from string
        ls = string_call.split(",")
        function_name = ls[0]

        if function_name not in self.exported_functions:
            raise FunctionNotImplemented(function_name)

        function = self.exported_functions[function_name]
        # get parameters
        args_str = ls[1:]
        # call the function
        self.run_with_args(function, args_str)
        return True

    def run_with_args(self, function, args):
        signature = inspect.signature(function)
        parameters = signature.parameters
        new_args = [self]
        for name, param in parameters.items():
            exp_type = param.annotation
            if exp_type is not inspect.Parameter.empty:
                try:
                    value = args[0]
                    args = args[1:]
                    value = exp_type(value)
                    new_args.append(value)
                except (TypeError, ValueError):
                    print(
                        f"Error: Can't convert the arg '{name}' al tipo {exp_type.__name__}"
                    )

        return function(*new_args)
