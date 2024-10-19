# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from reporting.event.state_event import StateEvent


class VariableValueAssignedEvent(StateEvent):
    def __init__(self, variable_name, variable_value, time) -> None:
        super().__init__(time)
        self._variable_name = variable_name
        self._variable_value = variable_value

    def variable_name(self):
        return self._variable_name

    def variable_value(self):
        return self._variable_value

    def process_with(self, monitor):
        return monitor.process_variable_value_assigned(self)

    @staticmethod
    def event_subtype():
        return "variable_value_assigned"

    @staticmethod
    def decode_with(decoder, encoded_event):
        return decoder.decode_variable_value_assignment_event(encoded_event)

    def serialized(self):
        return f"{self.time()},{self.event_type()},{self.event_subtype()},{self.variable_name()},{self.variable_value()}"
