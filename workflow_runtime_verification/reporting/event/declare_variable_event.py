from workflow_runtime_verification.reporting.event.workflow_event import WorkflowEvent


class DeclareVariableEvent(WorkflowEvent):
    def __init__(self, variable_name, variable_type, time) -> None:
        super().__init__(time)
        self._variable_name = variable_name
        self._variable_type = variable_type

    def variable_name(self):
        return self._variable_name

    def variable_type(self):
        return self._variable_type

    def process_with(self, monitor):
        return monitor.process_declare_variable(self)

    @staticmethod
    def event_subtype():
        return "declare_variable"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_declare_variable_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.variable_name()},{self.variable_type()}"
