from workflow_runtime_verification.reporting.event.state_event import (
    StateEvent,
)
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class VariableValueAssignedEvent(StateEvent):
    def __init__(self, variable_name, variable_value, time) -> None:
        super().__init__(time)
        self._variable_name = variable_name
        self._variable_value = variable_value

    def variable_name(self):
        return self._variable_name

    def variable_value(self):
        return self._variable_value

    def process_with(self, monitor):
        return monitor.process_variable_value_assigned(self)

    @staticmethod
    def event_subtype():
        return "variable_value_assigned"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_variable_value_assignment_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.variable_name()},{self.variable_value()}"
