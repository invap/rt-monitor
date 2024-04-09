from workflow_runtime_verification.reporting.event.timed_event import (
    TimedEvent,
)
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class ClockStartEvent(TimedEvent):
    def __init__(self, clock_name, time) -> None:
        super().__init__(time)
        self._clock_name = clock_name

    def clock_name(self):
        return self._clock_name

    def process_with(self, monitor):
        return monitor.process_clock_start(self)

    @staticmethod
    def event_subtype():
        return "clock_start"

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_clock_start_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.clock_name()}"
