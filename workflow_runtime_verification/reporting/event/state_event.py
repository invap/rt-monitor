from workflow_runtime_verification.reporting.event.event import Event
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class StateEvent(Event):
    def __init__(self, time) -> None:
        super().__init__(time)

    @staticmethod
    def event_type():
        return "state_event"

    @staticmethod
    def event_subtype():
        raise NotImplementedError

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_state_event(encoded_event)
