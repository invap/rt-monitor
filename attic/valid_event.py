from workflow_runtime_verification.reporting import Event


class ValidEvent(Event):
    def __init__(self, time) -> None:
        super().__init__()
        self._time = time

    @classmethod
    def event_type(cls):
        raise NotImplementedError

    @classmethod
    def event_subtype(cls):
        raise NotImplementedError

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        raise NotImplementedError
