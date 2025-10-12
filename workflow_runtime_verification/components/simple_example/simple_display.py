from workflow_runtime_verification.errors import FunctionNotImplemented


class SimpleDisplay:
    def write(self, _data):
        pass

    def stop(self):
        pass

    @staticmethod
    def state():
        return {}

    def process_high_level_call(self, call_data):
        call_data = call_data.split(",")
        function_name = call_data[0]
        if function_name == "display_write":
            self.write(call_data[1])
        else:
            raise FunctionNotImplemented(function_name)
