from workflow_runtime_verification.reporting.event.event import Event


class NoSubtypeError(Exception):
    pass


class ComponentEvent(Event):
    def __init__(self, component_name, data, time) -> None:
        super().__init__(time)
        self._component_name = component_name
        self._data = data

    def process_with(self, monitor):
        return monitor.process_hardware_event(self)

    def component_name(self):
        return self._component_name

    def data(self):
        return self._data

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
        return (
            f"{self.time()},{self.event_type()},"
            f"{self.component_name()},{self.data()}"
        )
