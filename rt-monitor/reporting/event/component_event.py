# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from reporting.event.event import Event


class NoSubtypeError(Exception):
    pass


class ComponentEvent(Event):
    def __init__(self, component_name, data, time) -> None:
        super().__init__(time)
        self._component_name = component_name
        self._data = data

    def process_with(self, monitor):
        return monitor.process_component_event(self)

    def component_name(self):
        return self._component_name

    def data(self):
        return self._data

    @staticmethod
    def event_type():
        return "component_event"

    @staticmethod
    def event_subtype():
        raise NoSubtypeError

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_component_event(encoded_event)

    def serialized(self):
        return (
            f"{self.time()},{self.event_type()},{self.component_name()},{self.data()}"
        )
