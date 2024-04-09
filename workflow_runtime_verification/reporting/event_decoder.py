from workflow_runtime_verification.errors import InvalidEventE
from workflow_runtime_verification.reporting.event.timed_event import TimedEvent
from workflow_runtime_verification.reporting.event.state_event import StateEvent
from workflow_runtime_verification.reporting.event.component_event import ComponentEvent
from workflow_runtime_verification.reporting.event.workflow_event import WorkflowEvent
from workflow_runtime_verification.reporting.event.declare_clock_event import DeclareClockEvent
from workflow_runtime_verification.reporting.event.clock_start_event import ClockStartEvent
from workflow_runtime_verification.reporting.event.clock_pause_event import ClockPauseEvent
from workflow_runtime_verification.reporting.event.clock_resume_event import ClockResumeEvent
from workflow_runtime_verification.reporting.event.clock_reset_event import ClockResetEvent
from workflow_runtime_verification.reporting.event.declare_variable_event import DeclareVariableEvent
from workflow_runtime_verification.reporting.event.variable_value_assigned_event import VariableValueAssignedEvent
from workflow_runtime_verification.reporting.event.task_started_event import TaskStartedEvent
from workflow_runtime_verification.reporting.event.task_finished_event import TaskFinishedEvent
from workflow_runtime_verification.reporting.event.checkpoint_reached_event import CheckpointReachedEvent
from workflow_runtime_verification.reporting.event.invalid_event import InvalidEvent


class EventDecoder:
    @staticmethod
    def decode(encoded_event):
        event_type = EventDecoder._decode_event_type(encoded_event)
        match event_type:
            case "timed_event":
                return TimedEvent.decode_with(encoded_event)
            case "state_event":
                return StateEvent.decode_with(encoded_event)
            case "component_event":
                return ComponentEvent.decode_with(encoded_event)
            case "workflow_event":
                return WorkflowEvent.decode_with(encoded_event)
            case "invalid":
                return InvalidEvent.decode_with(encoded_event)

    @staticmethod
    def decode_timed_event(encoded_event):
        timed_event_type = EventDecoder._decode_timed_event_type(encoded_event)
        match timed_event_type:
            case "declare_clock":
                return DeclareClockEvent.decode_with(encoded_event)
            case "clock_start":
                return ClockStartEvent.decode_with(encoded_event)
            case "clock_pause":
                return ClockPauseEvent.decode_with(encoded_event)
            case "clock_resume":
                return ClockResumeEvent.decode_with(encoded_event)
            case "clock_reset":
                return ClockResetEvent.decode_with(encoded_event)
            case _:
                raise InvalidEvent.decode_with(encoded_event)

    @staticmethod
    def decode_state_event(encoded_event):
        state_event_type = EventDecoder._decode_state_event_type(encoded_event)
        match state_event_type:
            case "declare_variable":
                return DeclareVariableEvent.decode_with(encoded_event)
            case "variable_value_assigned":
                return VariableValueAssignedEvent.decode_with(encoded_event)
            case _:
                raise InvalidEvent.decode_with(encoded_event)

    @staticmethod
    def decode_workflow_event(encoded_event):
        workflow_event_type = EventDecoder._decode_workflow_event_type(encoded_event)
        match workflow_event_type:
            case "task_started":
                return TaskStartedEvent.decode_with(encoded_event)
            case "task_finished":
                return TaskFinishedEvent.decode_with(encoded_event)
            case "checkpoint_reached":
                return CheckpointReachedEvent.decode_with(encoded_event)
            case _:
                raise InvalidEvent.decode_with(encoded_event)

    @staticmethod
    def decode_declare_clock_event(encoded_event):
        return DeclareClockEvent(
            EventDecoder._decode_clock_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_clock_start_event(encoded_event):
        return ClockStartEvent(
            EventDecoder._decode_clock_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_clock_pause_event(encoded_event):
        return ClockPauseEvent(
            EventDecoder._decode_clock_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_clock_resume_event(encoded_event):
        return ClockResumeEvent(
            EventDecoder._decode_clock_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_clock_reset_event(encoded_event):
        return ClockResetEvent(
            EventDecoder._decode_clock_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_declare_variable_event(encoded_event):
        return DeclareVariableEvent(
            EventDecoder._decode_variable_name(encoded_event),
            EventDecoder._decode_variable_type(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_variable_value_assignment_event(encoded_event):
        return VariableValueAssignedEvent(
            EventDecoder._decode_variable_name(encoded_event),
            EventDecoder._decode_variable_value(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_component_event(encoded_event):
        return ComponentEvent(
            EventDecoder._decode_component_name(encoded_event),
            EventDecoder._decode_event_data(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_task_started_event(encoded_event):
        return TaskStartedEvent(
            EventDecoder._decode_task_name(encoded_event),
            EventDecoder._decode_time(encoded_event)
        )

    @staticmethod
    def decode_task_finished_event(encoded_event):
        return TaskFinishedEvent(
            EventDecoder._decode_task_name(encoded_event),
            EventDecoder._decode_time(encoded_event)
        )

    @staticmethod
    def decode_checkpoint_reached_event(encoded_event):
        return CheckpointReachedEvent(
            EventDecoder._decode_checkpoint_name(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def decode_invalid_event(encoded_event):
        return InvalidEvent(
            EventDecoder._decode_event_data(encoded_event),
            EventDecoder._decode_time(encoded_event),
        )

    @staticmethod
    def _decode_event_type(encoded_event):
        try:
            return encoded_event.split(",")[1]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_timed_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_state_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_workflow_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_clock_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_variable_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_variable_type(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[2].split(",")
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_variable_value(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[2]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_component_name(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_task_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_checkpoint_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEventE(encoded_event)

    @staticmethod
    def _decode_time(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            t = encoded_parameters[0]
        except IndexError:
            raise InvalidEventE(encoded_event)

        return int(t)

    @staticmethod
    def _decode_event_data(encoded_event):
        try:
            event_data_as_array = encoded_event.split(",")[3:]
        except IndexError:
            raise InvalidEventE(encoded_event)

        event_data_with_escaped_characters = ",".join(event_data_as_array)
        event_data = bytes(event_data_with_escaped_characters, "utf-8").decode(
            "unicode_escape"
        )
        return event_data

    @staticmethod
    def _encoded_event_parameters(encoded_event):
        try:
            encoded_time = encoded_event.split(",")[0]
            encoded_parameters_without_time = encoded_event.split(",")[3:]
        except IndexError:
            raise InvalidEventE(encoded_event)

        encoded_parameters = [encoded_time] + encoded_parameters_without_time
        return encoded_parameters
