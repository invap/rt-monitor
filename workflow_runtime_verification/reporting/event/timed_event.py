from workflow_runtime_verification.reporting.event.event import Event
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class TimedEvent(Event):
    def __init__(self, time) -> None:
        super().__init__(time)

    @staticmethod
    def event_type():
        return "timed_event"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_timed_event(encoded_event)
