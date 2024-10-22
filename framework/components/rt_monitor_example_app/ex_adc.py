# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import inspect

import numpy as np

from errors.component_errors import FunctionNotImplementedError
from framework.components.component import SelfLoggableComponent
from framework.components.rt_monitor_example_app import ex_adcVisual
from novalue import NoValue


class adc(SelfLoggableComponent):
    def __init__(self, visual):
        super().__init__(visual)
        AcumCalib = 0
        Calib = 0
        ContCalib = 0
        self._adc_read = NoValue
        # statistics variables
        self.__total_values_read = 0
        self.__current_value = 0
        if self._visual:
            # create the visualization features associated
            self.__visualADC = ex_adcVisual.adcVisual(parent=self, adc_component=self)
            self.__visualADC.Show()

    def stop(self):
        if self._visual:
            # closes the visualization features associated
            self.__visualADC.close()

    def state(self):
        state = {"adc_read": ("Int", self._adc_read)}
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
            raise FunctionNotImplementedError(function_name)

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

    def process_log(self, log_file, mark):
        current_pos = log_file.tell()
        line = log_file.readline()
        while line:
            split_line = line.strip().split(",")
            if mark <= int(split_line[0]):
                break
            self._process_event(split_line[1:])
            current_pos = log_file.tell()
            line = log_file.readline()
        log_file.seek(current_pos)

    def _process_event(self, event):
        self._adc_read = event[0]
