# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import inspect
import logging
from abc import ABC, abstractmethod

from rt_monitor.errors.component_errors import FunctionNotImplementedError


class Component(ABC):
    exported_functions = {}

    def __init__(self):
        pass

    @abstractmethod
    def state(self):
        pass

    def get_status(self):
        raise NotImplementedError

    def process_high_level_call(self, string_call):
        ls = string_call.split(",")
        function_name = ls[0]

        if function_name not in self.exported_functions:
            logging.error(f"Function [ {function_name} ] not implemented by component [ {self.__class__.__name__} ].")
            raise FunctionNotImplementedError(function_name)

        function = self.exported_functions[function_name]
        args_str = ls[1:]
        self.run_with_args(function, args_str)
        return True

    def run_with_args(self, function, args):
        signature = inspect.signature(function)
        parameters = signature.parameters
        new_args = [self]
        for name, param in parameters.items():
            exp_type = param.annotation
            if exp_type is not inspect.Parameter.empty:
                if not args:
                    break  # No more args to process
                try:
                    value = args[0]
                    args = args[1:]
                    value = exp_type(value)
                    new_args.append(value)
                except (TypeError, ValueError) as e:
                    logging.error(f"Error converting arg '{name}' to {exp_type.__name__}: {e}")
                    raise
        return function(*new_args)
