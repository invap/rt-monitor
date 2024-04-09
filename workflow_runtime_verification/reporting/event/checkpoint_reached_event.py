from workflow_runtime_verification.reporting.event.workflow_event import (
    WorkflowEvent,
)
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class CheckpointReachedEvent(WorkflowEvent):
    def __init__(self, name, time) -> None:
        super().__init__(time)
        self._name = name

    def name(self):
        return self._name

    def process_with(self, monitor):
        return monitor.process_checkpoint_reached(self)

    @staticmethod
    def event_subtype():
        return "checkpoint_reached"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_checkpoint_reached_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
