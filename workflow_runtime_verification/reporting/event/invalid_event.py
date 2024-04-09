from workflow_runtime_verification.reporting.event.event import Event
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class InvalidEvent(Event):
    def __init__(self, data, time) -> None:
        super().__init__(time)
        self._data = data

    def data(self):
        return self._data

    def process_with(self, monitor):
        return monitor.process_invalid_event(self)

    @staticmethod
    def event_type():
        return "invalid"

    @staticmethod
    def event_subtype():
        raise NotImplementedError

    @staticmethod
    def decode_with(encoded_event):
        return EventDecoder.decode_invalid_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.data()}"
