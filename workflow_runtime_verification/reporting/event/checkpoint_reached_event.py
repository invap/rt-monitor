from workflow_runtime_verification.reporting.event.workflow_event import (
    WorkflowEvent,
)


class CheckpointReachedEvent(WorkflowEvent):
    def __init__(self, name, time) -> None:
        super().__init__(time)
        self._name = name

    def name(self):
        return self._name

    def process_with(self, monitor):
        return monitor.process_checkpoint_reached(self)

    @classmethod
    def event_subtype(cls):
        return "checkpoint_reached"

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        return decoder.decode_checkpoint_reached_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
