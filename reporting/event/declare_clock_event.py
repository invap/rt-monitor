# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from reporting.event.timed_event import TimedEvent


class DeclareClockEvent(TimedEvent):
    def __init__(self, clock_name, time) -> None:
        super().__init__(time)
        self._clock_name = clock_name

    def clock_name(self):
        return self._clock_name

    def process_with(self, monitor):
        return monitor.process_declare_clock(self)

    @staticmethod
    def event_subtype():
        return "declare_clock"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_declare_clock_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.clock_name()}"
