from workflow_runtime_verification.reporting.event.event import Event

class TimedEvent(Event):
    def __init__(self, time) -> None:
        super().__init__(time)

    @staticmethod
    def event_type():
        return "timed_event"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_timed_event(encoded_event)