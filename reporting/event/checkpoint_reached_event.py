# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from reporting.event.process_event import ProcessEvent


class CheckpointReachedEvent(ProcessEvent):
    def __init__(self, name, time) -> None:
        super().__init__(time)
        self._name = name

    def name(self):
        return self._name

    def process_with(self, monitor):
        return monitor.process_checkpoint_reached(self)

    @staticmethod
    def event_subtype():
        return "checkpoint_reached"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_checkpoint_reached_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.name()}"
