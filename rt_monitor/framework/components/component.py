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
    def stop(self):
        raise NotImplementedError

    @abstractmethod
    def state(self):
        raise NotImplementedError

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


class VisualComponent(Component, ABC):
    def __init__(self, visual_component_class, visual=False):
        super().__init__()
        self._visual = visual
        self._visual_component_class = visual_component_class
        # self._visual_component has to be initialized at the end of method __init__ of the visual component
        # invoking method initialize_visual_component,
        self._visual_component = None

    def initialize_visual_component(self):
        if self._visual:
            # Create the visualization features associated
            self._visual_component = self._visual_component_class(self, self)
            self._visual_component.Show()

    def visual(self):
        return self._visual

    def visual_component(self):
        return self._visual_component

    # Any subclass of Visual Component must implement the stop() method and has to have some code
    # like the one below for closing the visual feature before destroying the component.
    #
    # def stop(self):
    #     if self._visual:
    #         Closes the visualization features associated.
    #         self._visual_component.timer.Stop()
    #         self._visual_component.Hide()


class SelfLoggingComponent(Component, ABC):
    def __init__(self):
        super().__init__()

    @abstractmethod
    def process_log(self, log_file, mark):
        raise NotImplementedError
