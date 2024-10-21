# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from reporting.event.checkpoint_reached_event import (
    CheckpointReachedEvent,
)
from reporting.event.component_event import ComponentEvent
from reporting import (
    DeclareVariableEvent,
)
from reporting.event.task_finished_event import (
    TaskFinishedEvent,
)
from reporting.event.task_started_event import (
    TaskStartedEvent,
)
from reporting.event.variable_value_assigned_event import (
    VariableValueAssignedEvent,
)
from attic.tests.test_object_factories.test_name_and_value_factory import (
    TestNameAndValueFactory,
)


class TestEncodedEventFactory(TestNameAndValueFactory):
    def time(self):
        return 0

    def event_reporter(self):
        return EventReporter()

    def encoded_event_with_invalid_type(self):
        return "invalid_encoded_event_type()"

    def encoded_event_with_no_parameters(self):
        return f"{CheckpointReachedEvent.event_type()}("

    def encoded_event_without_time_delimiter(self):
        return f"{CheckpointReachedEvent.event_type()}(no_time_delimiter)"

    def task_finished_encoded_event(self, task_name):
        return self.event_reporter().report_task_finished(task_name, self.time())

    def task_started_encoded_event(self, task_name):
        return self.event_reporter().report_task_started(task_name, self.time())

    def declared_variable_encoded_event(self, variable_name, variable_type):
        return self.event_reporter().report_declared_variable(
            variable_name,
            variable_type,
            self.time(),
        )

    def variable_value_assigned_encoded_event(self, variable_name, variable_value):
        return self.event_reporter().report_variable_value_assigned(
            variable_name,
            variable_value,
            self.time(),
        )

    def checkpoint_reached_encoded_event(self, checkpoint_name):
        return self.event_reporter().report_checkpoint_reached(
            checkpoint_name,
            self.time(),
        )

    def value_assignment_event_without_value_delimiter(self):
        return (
            f"{VariableValueAssignedEvent.event_type()}"
            f"(no_value_delimiter@{self.time()})"
        )

    def component_encoded_event(self, component_name, data):
        return self.event_reporter().report_component_event(
            component_name, data, self.time()
        )

    def report_without_task_events(self):
        return [
            self.declared_variable_encoded_event(
                self.variable_name(), self.variable_type()
            ),
            self.variable_value_assigned_encoded_event(
                self.variable_name(), self.variable_value()
            ),
        ]

    def event_report_with_many_variables(self):
        return [
            self.declared_variable_encoded_event(
                self.variable_name(), self.variable_type()
            ),
            self.declared_variable_encoded_event(
                self.another_variable_name(), self.variable_type()
            ),
            self.variable_value_assigned_encoded_event(
                self.variable_name(), self.variable_value()
            ),
            self.variable_value_assigned_encoded_event(
                self.another_variable_name(),
                self.another_variable_value(),
            ),
        ]


class EventReporter:
    def report_task_started(self, task_name, time):
        return TaskStartedEvent(task_name, time).serialized()

    def report_task_finished(self, task_name, time):
        return TaskFinishedEvent(task_name, time).serialized()

    def report_declared_variable(self, variable_name, variable_type, time):
        return DeclareVariableEvent(variable_name, variable_type, time).serialized()

    def report_checkpoint_reached(self, checkpoint_name, time):
        return CheckpointReachedEvent(checkpoint_name, time).serialized()

    def report_variable_value_assigned(self, variable_name, variable_value, time):
        return VariableValueAssignedEvent(
            variable_name, variable_value, time
        ).serialized()

    def report_component_event(self, component_name, data, time):
        return ComponentEvent(component_name, data, time).serialized()
