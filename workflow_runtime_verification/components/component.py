import inspect

from workflow_runtime_verification.errors import FunctionNotImplemented


class Component:
    def exported_functions(self):
        raise NotImplementedError()

    def stop(self):
        raise NotImplementedError

    def state(self):
        raise NotImplementedError

    def process_high_level_call(self, call_data):
        """
        This method receive as parameter a string_call containing a sequence of values,
        the first one is the class method name (e.g. lectura), then a lists of
        parameters for its call.
        """
        ls = call_data.split(",")
        function_name = ls[0]

        if function_name not in self.exported_functions():
            raise FunctionNotImplemented(function_name)

        function = self.exported_functions()[function_name]
        args_str = ls[1:]
        self.run_with_args(function, args_str)
        return True

    def run_with_args(self, function, args):
        signature = inspect.signature(function)
        parameters = signature.parameters
        new_args = []
        for name, param in parameters.items():
            exp_type = param.annotation
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
