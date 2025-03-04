# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from errors.event_decoder_errors import InvalidEvent
from reporting.event.timed_event import TimedEvent
from reporting.event.state_event import StateEvent
from reporting.event.component_event import ComponentEvent
from reporting.event.process_event import ProcessEvent
from reporting.event.clock_start_event import ClockStartEvent
from reporting.event.clock_pause_event import ClockPauseEvent
from reporting.event.clock_resume_event import ClockResumeEvent
from reporting.event.clock_reset_event import ClockResetEvent
from reporting.event.variable_value_assigned_event import VariableValueAssignedEvent
from reporting.event.task_started_event import TaskStartedEvent
from reporting.event.task_finished_event import TaskFinishedEvent
from reporting.event.checkpoint_reached_event import CheckpointReachedEvent


#Raises: InvalidEvent()
class EventDecoder:
    @staticmethod
    def decode(encoded_event):
        event_type = EventDecoder._decode_event_type(encoded_event)
        match event_type:
            case "timed_event":
                return TimedEvent.decode_with(EventDecoder, encoded_event)
            case "state_event":
                return StateEvent.decode_with(EventDecoder, encoded_event)
            case "component_event":
                return ComponentEvent.decode_with(EventDecoder, encoded_event)
            case "process_event":
                return ProcessEvent.decode_with(EventDecoder, encoded_event)
            case "invalid":
                raise InvalidEvent(encoded_event)
            case _:
                # The execution should never match this case because the rt_reporter injects "invalid"
                # when the event reported is not af any of the above types.
                raise InvalidEvent(encoded_event)

    @staticmethod
    def decode_timed_event(encoded_event):
        timed_event_type = EventDecoder._decode_timed_event_type(encoded_event)
        match timed_event_type:
            case "clock_start":
                return ClockStartEvent.decode_with(EventDecoder, encoded_event)
            case "clock_pause":
                return ClockPauseEvent.decode_with(EventDecoder, encoded_event)
            case "clock_resume":
                return ClockResumeEvent.decode_with(EventDecoder, encoded_event)
            case "clock_reset":
                return ClockResetEvent.decode_with(EventDecoder, encoded_event)
            case _:
                raise InvalidEvent(encoded_event)

    @staticmethod
    def decode_state_event(encoded_event):
        state_event_type = EventDecoder._decode_state_event_type(encoded_event)
        match state_event_type:
            case "variable_value_assigned":
                return VariableValueAssignedEvent.decode_with(EventDecoder, encoded_event)
            case _:
                raise InvalidEvent(encoded_event)

    @staticmethod
    def decode_process_event(encoded_event):
        process_event_type = EventDecoder._decode_process_event_type(encoded_event)
        match process_event_type:
            case "task_started":
                return TaskStartedEvent.decode_with(EventDecoder, encoded_event)
            case "task_finished":
                return TaskFinishedEvent.decode_with(EventDecoder, encoded_event)
            case "checkpoint_reached":
                return CheckpointReachedEvent.decode_with(EventDecoder, encoded_event)
            case _:
                raise InvalidEvent(encoded_event)

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
    def _decode_event_type(encoded_event):
        try:
            return encoded_event.split(",")[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_timed_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_state_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_process_event_type(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_clock_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_variable_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_variable_type(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[2].split(",")
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_variable_value(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[2]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_component_name(encoded_event):
        try:
            return encoded_event.split(",")[2]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_task_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_checkpoint_name(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            return encoded_parameters[1]
        except IndexError:
            raise InvalidEvent(encoded_event)

    @staticmethod
    def _decode_time(encoded_event):
        encoded_parameters = EventDecoder._encoded_event_parameters(encoded_event)
        try:
            t = encoded_parameters[0]
        except IndexError:
            raise InvalidEvent(encoded_event)

        return int(t)

    @staticmethod
    def _decode_event_data(encoded_event):
        try:
            event_data_as_array = encoded_event.split(",")[3:]
        except IndexError:
            raise InvalidEvent(encoded_event)

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
            raise InvalidEvent(encoded_event)

        encoded_parameters = [encoded_time] + encoded_parameters_without_time
        return encoded_parameters
