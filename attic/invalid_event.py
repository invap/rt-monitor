from workflow_runtime_verification.reporting.event.component_event import NoSubtypeError
from workflow_runtime_verification.reporting.event.event import Event


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
