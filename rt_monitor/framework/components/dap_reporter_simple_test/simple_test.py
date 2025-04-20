import inspect

from rt_monitor.errors.component_errors import FunctionNotImplementedError
from rt_monitor.framework.components.component import VisualComponent


class component(VisualComponent):
    def __init__(self, visual_component_class, visual):
        super().__init__(visual_component_class, visual)
        self.__value = 0
        # Initializes the visual feature of the class
        self.initialize_visual_component()

    def state(self):
        state = {"value": ("Int", self.__value)}
        return state

    def component_func(self, x, y):
        self.__value = x + y

    def get_status(self):
        return [self.__value]

    # component exported methods
    exported_functions = {"component_func": component_func}

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

    def stop(self):
        pass
