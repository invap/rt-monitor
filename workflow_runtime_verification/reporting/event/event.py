class Event:
    def __init__(self, time):
        self._time = time

    def time(self):
        return self._time

    def process_with(self, monitor):
        raise NotImplementedError

    @staticmethod
    def event_type():
        raise NotImplementedError

    @staticmethod
    def event_subtype():
        raise NotImplementedError

    @staticmethod
    def decode_with(decoder, encoded_event):
        raise NotImplementedError

    def serialized(self):
        raise NotImplementedError
