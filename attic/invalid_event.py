from workflow_runtime_verification.reporting.event.event import Event
from workflow_runtime_verification.reporting.event.hardware_event import NoSubtypeError


class InvalidEventError(Exception):
    pass


class InvalidEvent(Event):
    def serialized(self):
        return self.event_type()

    def process_with(self, monitor):
        raise InvalidEventError

    @classmethod
    def event_type(cls):
        return "invalid"

    @classmethod
    def event_subtype(cls):
        raise NoSubtypeError

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        return cls()