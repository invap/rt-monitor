class Event:
    def __init__(self, time):
        self._time = time

    def time(self):
        return self._time

    def serialized(self):
        raise NotImplementedError

    def process_with(self, monitor):
        raise NotImplementedError

    @classmethod
    def event_type(cls):
        raise NotImplementedError

    @classmethod
    def event_subtype(cls):
        raise NotImplementedError

    @classmethod
    def decode_with(cls, decoder, encoded_event):
        raise NotImplementedError
