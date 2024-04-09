from workflow_runtime_verification.reporting.event.event import Event
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class WorkflowEvent(Event):
    def __init__(self, time) -> None:
        super().__init__(time)

    @staticmethod
    def event_type():
        return "workflow_event"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_workflow_event(encoded_event)
