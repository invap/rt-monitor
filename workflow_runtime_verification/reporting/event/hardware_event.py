from workflow_runtime_verification.reporting.event.event import Event


class NoSubtypeError(Exception):
    pass


class HardwareEvent(Event):
    def __init__(self, hardware_data, time) -> None:
        super().__init__(time)
        self._hardware_data = hardware_data

    def process_with(self, monitor):
        return monitor.process_hardware_event(self)

    def hardware_data(self):
        return self._hardware_data

    @classmethod
    def event_type(cls):
        return "hardware_event"

    @classmethod
    def event_subtype(cls):
        raise NoSubtypeError

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        return decoder.decode_hardware_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self._hardware_data}"
