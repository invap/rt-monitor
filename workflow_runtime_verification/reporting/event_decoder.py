from workflow_runtime_verification.reporting.event.checkpoint_reached_event import (
    CheckpointReachedEvent,
)
from workflow_runtime_verification.reporting.event.declare_variable_event import (
    DeclareVariableEvent,
)
from workflow_runtime_verification.reporting.event.hardware_event import (
    ComponentEvent,
)
from workflow_runtime_verification.reporting.event.task_finished_event import (
    TaskFinishedEvent,
)
from workflow_runtime_verification.reporting.event.task_started_event import (
    TaskStartedEvent,
)
from workflow_runtime_verification.reporting.event.variable_value_assigned_event import (
    VariableValueAssignedEvent,
)


class InvalidEvent(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def event(self):
        return self._event


class EventDecoder:
    def decode(self, encoded_event):
        event_type = self._decode_event_type(encoded_event)
        match event_type:
            case "hardware_event":
                return self.decode_component_event(encoded_event)
            case "workflow_event":
                return self.decode_workflow_event(encoded_event)
            case "invalid":
                raise InvalidEvent(encoded_event)

    def decode_workflow_event(self, encoded_event):
        workflow_event_type = self._decode_workflow_event_type(encoded_event)
        match workflow_event_type:
            case "task_started":
                return self.decode_task_started_event(encoded_event)
            case "task_finished":
                return self.decode_task_finished_event(encoded_event)
            case "checkpoint_reached":
                return self.decode_checkpoint_reached_event(encoded_event)
            case "declare_variable":
                return self.decode_declare_variable_event(encoded_event)
            case "variable_value_assigned":
                return self.decode_variable_value_assignment_event(encoded_event)

    def decode_component_event(self, encoded_event):
        return ComponentEvent(
            self._decode_hardware_component_name(encoded_event),
            self._decode_hardware_event_data(encoded_event),
            self._decode_time(encoded_event),
        )

    def decode_task_started_event(self, encoded_event):
        return TaskStartedEvent(
            self._decode_task_name(encoded_event), self._decode_time(encoded_event)
        )

    def decode_task_finished_event(self, encoded_event):
        return TaskFinishedEvent(
            self._decode_task_name(encoded_event), self._decode_time(encoded_event)
        )

    def decode_declare_variable_event(self, encoded_event):
        return DeclareVariableEvent(
            self._decode_variable_name(encoded_event),
            self._decode_variable_type(encoded_event),
            self._decode_time(encoded_event),
        )

    def decode_variable_value_assignment_event(self, encoded_event):
        return VariableValueAssignedEvent(
            self._decode_variable_name(encoded_event),
            self._decode_variable_value(encoded_event),
            self._decode_time(encoded_event),
        )

    def decode_checkpoint_reached_event(self, encoded_event):
        return CheckpointReachedEvent(
            self._decode_checkpoint_name(encoded_event),
            self._decode_time(encoded_event),
        )

    def _decode_event_type(self, encoded_event):
        try:
            return encoded_event.split(",")[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    def _decode_workflow_event_type(self, encoded_event):
        return encoded_event.split(",")[2]

    def _decode_task_name(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        return encoded_parameters[1]

    def _decode_variable_name(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        return encoded_parameters[1]

    def _decode_variable_type(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        return encoded_parameters[2].split(",")

    def _decode_variable_value(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        return encoded_parameters[2]

    def _decode_checkpoint_name(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        return encoded_parameters[1]

    def _decode_time(self, encoded_event):
        encoded_parameters = self._encoded_task_event_parameters(encoded_event)
        serialized_time = encoded_parameters[0]

        return int(serialized_time)

    def _decode_hardware_component_name(self, encoded_event):
        return encoded_event.split(",")[2]

    def _decode_hardware_event_data(self, encoded_event):
        event_data_as_array = encoded_event.split(",")[3:]
        event_data_with_escaped_characters = ",".join(event_data_as_array)

        event_data = bytes(event_data_with_escaped_characters, "utf-8").decode(
            "unicode_escape"
        )
        return event_data

    @staticmethod
    def _encoded_task_event_parameters(encoded_event):
        encoded_time = encoded_event.split(",")[0]
        encoded_parameters_without_time = encoded_event.split(",")[3:]
        encoded_parameters = [encoded_time] + encoded_parameters_without_time
        return encoded_parameters
