# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import threading

from errors.clock_errors import (
    ClockError,
    UndeclaredClockError,
    ClockWasAlreadyStartedError,
    ClockWasNotStartedError,
    ClockWasAlreadyPausedError,
    ClockWasNotPausedError
)
from errors.component_errors import FunctionNotImplementedError
from errors.evaluator_errors import BuildSpecificationError
from errors.event_decoder_errors import InvalidEvent
from errors.monitor_errors import (
    UndeclaredComponentVariableError,
    UnknownVariableClassError,
    UndeclaredVariableError,
    TaskDoesNotExistError,
    CheckpointDoesNotExistError,
    AbortRun,
    ComponentDoesNotExistError,
    ComponentError
)
from logging_configuration import LoggingLevel
from framework.clock import Clock
from reporting.event_decoder import EventDecoder
from novalue import NoValue
from property_evaluator.evaluator import Evaluator


class Monitor(threading.Thread):
    PROCESS_IDLE_STATE = "process_idle"
    PROCESS_FINISHED = "process_finished"

    TASK_STARTED_SUFFIX = "_started"
    TASK_FINISHED_SUFFIX = "_finished"
    CHECKPOINT_REACHED_SUFFIX = "_reached"

    # Raises: UndeclaredComponentVariableError(), UnknownVariableClassError()
    def __init__(self, framework, reports_map):
        super().__init__()
        # Analysis framework
        self._framework = framework
        # revent reports
        self._reports_map = reports_map
        # Events for controlling the execution of the monitor (TBS by set_events)
        self._pause_event = None
        self._has_paused_event = None
        self._stop_event = None
        self._has_stopped_event = None
        # Variables for stats
        self._amount_of_events_to_verify = len(reports_map["main"].readlines())
        # Returns the pointer to the beginning because readlines() moves the pointer to the end.
        reports_map["main"].seek(0)
        self._amount_of_processed_events = 0
        # State
        self._process_state = set()
        self._execution_state = {}
        self._timed_state = {}
        # Build the state dictionary discarding the variable class
        # (i.e., self._framework.process().get_variables()[variable][0]) {State|Component|Clock}.
        for variable in self._framework.process().variables():
            match self._framework.process().variables()[variable][0]:
                case "State":
                    self._execution_state[variable] = (self._framework.process().variables()[variable][1], NoValue)
                case "Component":
                    # check whether all component variables appearing in the formulas in the process
                    if not any([variable in self._framework.components()[component].state() for component in
                                self._framework.components()]):
                        logging.error(f"Variable [ {variable} ] not declared in any component.")
                        raise UndeclaredComponentVariableError()
                case "Clock":
                    self._timed_state[variable] = (
                        self._framework.process().variables()[variable][1], Clock(variable)
                    )
                case _:
                    logging.error(
                        f"Variables class [ {self._framework.process().variables()[variable][0]} ] unsupported.")
                    raise UnknownVariableClassError()
        # Formula evaluator
        self._evaluator = Evaluator(
            self._framework.components(),
            self._process_state,
            self._execution_state,
            self._timed_state
        )

    def get_event_count(self):
        return [self._amount_of_events_to_verify, self._amount_of_processed_events]

    def set_events(self, pause_event, has_pause_event, stop_event, has_stoped_event):
        self._pause_event = pause_event
        self._has_paused_event = has_pause_event
        self._stop_event = stop_event
        self._has_stopped_event = has_stoped_event

    # Raises: AbortRun()
    def run(self):
        is_a_valid_report = True
        for line in self._reports_map["main"]:
            # Decode next event.
            try:
                decoded_event = EventDecoder.decode(line.strip())
            except InvalidEvent as e:
                logging.critical(f"Invalid event [ {e.event().serialized()} ].")
                raise AbortRun()
            logging.info(f"Processing: {decoded_event.serialized()}")
            mark = decoded_event.time()
            # Process the events of all self-logging components until time mark of the next event.
            for component in self._reports_map:
                if not component == "main":
                    logging.info(f"Processing log for self-logging component: {component}")
                    self._framework.components()[component].process_log(self._reports_map[component], mark)
            # Process main event.
            try:
                is_a_valid_report = decoded_event.process_with(self)
            # Execution state related exceptions.
            except UndeclaredVariableError:
                logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            # Clock related exceptions.
            except ClockError:
                logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            # Task related exceptions.
            except TaskDoesNotExistError:
                logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            # Checkpoint related exceptions.
            except CheckpointDoesNotExistError:
                logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            # Component related exceptions.
            except ComponentDoesNotExistError:
                logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            except ComponentError:
                logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                raise AbortRun()
            else:
                # Thread control.
                if not self._pause_event.is_set():
                    # Notifies that the analysis has gracefully paused.
                    self._has_paused_event.clear()
                    self._pause_event.wait()
                    self._has_paused_event.set()
                if not self._stop_event.is_set():
                    # Notifies that the analysis has gracefully stopped.
                    self._has_stopped_event.clear()
                    break
                # There was no exception in processing the event.
                self._amount_of_processed_events = self._amount_of_processed_events + 1
                # Action if the event cause the verification to fail.
                if not is_a_valid_report:
                    logging.info(
                        f"The following event caused the verification to fail: "
                        f"[ {decoded_event.serialized()} ]"
                    )
                    break
        self._framework.stop_components()
        # Log the result of when the verification finishes.
        if self._stop_event.is_set():
            if not is_a_valid_report:
                logging.log(LoggingLevel.ANALYSIS, "Verification completed UNSUCCESSFULLY.")
            else:
                logging.log(LoggingLevel.ANALYSIS, "Verification completed SUCCESSFULLY.")

    # Raises: TaskDoesNotExistError()
    # Propagates: AbortRun() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        if not self._framework.process().task_exists(task_name):
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        can_start = self._task_can_start(task_name)
        task_specification = self._framework.process().task_specification_named(task_name)
        preconditions_are_met = self._are_all_properties_satisfied(
            task_started_event.time(),
            task_specification.preconditions(),
        )
        self._update_process_state_with_started_task(task_started_event)
        return can_start and preconditions_are_met

    def _update_process_state_with_started_task(self, task_started_event):
        task_name = task_started_event.name()
        self._process_state.clear()
        self._process_state.add(task_name + Monitor.TASK_STARTED_SUFFIX)

    # Raises: TaskDoesNotExistError()
    # Propagates: AbortRun() from _are_all_properties_satisfied
    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()
        if not self._framework.process().task_exists(task_name):
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        had_previously_started = self._task_had_started(task_name)
        task_specification = self._framework.process().task_specification_named(task_name)
        postconditions_are_met = self._are_all_properties_satisfied(
            task_finished_event.time(),
            task_specification.postconditions(),
        )
        self._update_process_state_with_finished_task(task_finished_event)
        return had_previously_started and postconditions_are_met

    def _update_process_state_with_finished_task(self, task_finished_event):
        task_name = task_finished_event.name()
        self._process_state.clear()
        self._process_state.add(task_name + Monitor.TASK_FINISHED_SUFFIX)

    # Propagates: AbortRun() from _is_property_satisfied
    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        if (not self._framework.process().global_checkpoint_exists(checkpoint_name) and
                not self._framework.process().local_checkpoint_exists(checkpoint_name)):
            logging.error(f"Checkpoint [ {checkpoint_name} ] does not exist.")
            raise CheckpointDoesNotExistError()
        if self._framework.process().global_checkpoint_exists(checkpoint_name):
            return self._process_global_checkpoint_reached(checkpoint_reached_event)
        if self._framework.process().local_checkpoint_exists(checkpoint_name):
            return self._process_local_checkpoint_reached(checkpoint_reached_event)

    # Propagates: AbortRun() from _are_all_properties_satisfied
    def _process_global_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        can_be_reached = self._global_checkpoint_can_be_reached(checkpoint_name)
        checkpoint = self._framework.process().global_checkpoint_named(checkpoint_name)
        properties_are_met = self._are_all_properties_satisfied(checkpoint_reached_event.time(),
                                                                checkpoint.properties())
        self._update_process_state_with_reached_global_checkpoint(checkpoint_reached_event)
        return can_be_reached and properties_are_met

    # Propagates: AbortRun() from _are_all_properties_satisfied
    def _process_local_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        can_be_reached = self._local_checkpoint_can_be_reached(checkpoint_name)
        checkpoint = self._framework.process().local_checkpoint_named(checkpoint_name)
        properties_are_met = self._are_all_properties_satisfied(checkpoint_reached_event.time(),
                                                                checkpoint.properties())
        started_task_name = self._started_task_name_from_state()
        self._update_process_state_with_reached_local_checkpoint(checkpoint_reached_event, started_task_name)
        return can_be_reached and properties_are_met

    # Raises: UndeclaredVariableError()
    def process_variable_value_assigned(self, variable_value_assigned_event):
        variable_name = variable_value_assigned_event.variable_name()
        variable_value = variable_value_assigned_event.variable_value()
        if variable_name not in self._execution_state:
            logging.error(f"Variable [ {variable_name} ] was not declared.")
            raise UndeclaredVariableError()
        self._execution_state[variable_name] = (self._execution_state[variable_name][0], variable_value)
        return True

    # Raises: ComponentDoesNotExistError(), ComponentError()
    def process_component_event(self, component_event):
        component_data = component_event.data()
        component_name = component_event.component_name()
        if component_name not in self._framework.components():
            logging.error(f"Component [ {component_name} ] does not exist.")
            raise ComponentDoesNotExistError()
        component = self._framework.components()[component_name]
        try:
            component.process_high_level_call(component_data)
        except FunctionNotImplementedError as e:
            logging.error(
                f"Function [ {e.function_name()} ] is not implemented for component [ {component_name} ]."
            )
            raise ComponentError()
        return True

    # Raises: ClockError()
    def process_clock_start(self, clock_start_event):
        clock_name = clock_start_event.clock_name()
        if clock_name not in self._timed_state:
            logging.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].start(clock_start_event.time())
        except ClockWasAlreadyStartedError:
            logging.error(f"Clock [ {clock_name} ] was already started.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_pause(self, clock_pause_event):
        clock_name = clock_pause_event.clock_name()
        if clock_name not in self._timed_state:
            logging.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].pause(clock_pause_event.time())
        except ClockWasNotStartedError:
            logging.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasAlreadyPausedError:
            logging.error(f"Clock [ {clock_name} ] was already paused.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_resume(self, clock_resume_event):
        clock_name = clock_resume_event.clock_name()
        if clock_name not in self._timed_state:
            logging.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].resume(clock_resume_event.time())
        except ClockWasNotStartedError:
            logging.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasNotPausedError:
            logging.error(f"Clock [ {clock_name} ] was not paused.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_reset(self, clock_reset_event):
        clock_name = clock_reset_event.clock_name()
        if clock_name not in self._timed_state:
            logging.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].reset(clock_reset_event.time())
        except ClockWasNotStartedError:
            logging.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        return True

    def _update_process_state_with_reached_global_checkpoint(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        self._process_state = {
            state_word
            for state_word in self._process_state
            if not state_word.endswith(Monitor.CHECKPOINT_REACHED_SUFFIX)
        }
        self._process_state.add(checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX)

    def _update_process_state_with_reached_local_checkpoint(self, checkpoint_reached_event, task_name):
        checkpoint_name = checkpoint_reached_event.name()
        self._process_state = {
            state_word
            for state_word in self._process_state
            if not state_word.endswith(Monitor.CHECKPOINT_REACHED_SUFFIX)
        }
        self._process_state.add(task_name + "." + checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX)

    # Propagates: AbortRun() from _is_property_satisfied
    def _are_all_properties_satisfied(self, event_time, logic_properties):
        neg_properties_sat = False
        for logic_property in logic_properties:
            if neg_properties_sat:
                break
            neg_properties_sat = self._is_property_satisfied(event_time, logic_property)
        return not neg_properties_sat

    # Raises: AbortRun()
    def _is_property_satisfied(self, event_time, logic_property):
        logging.log(LoggingLevel.ANALYSIS, f"Checking property {logic_property.name()}...")
        try:
            negation_is_sat = self._evaluator.eval(logic_property, event_time)
        except BuildSpecificationError:
            logging.error(f"Error evaluating formula [ {logic_property.name()} ]")
            raise AbortRun()
        if not negation_is_sat:
            logging.log(LoggingLevel.ANALYSIS, f"Property {logic_property.name()} PASSED")
        else:
            logging.log(LoggingLevel.ANALYSIS, f"Property {logic_property.name()} FAILED")
        return negation_is_sat

    # ToDo: Reformulate the record of the evolution of the process
    def _task_can_start(self, task_name):
        return self._is_process_state_valid_for_reaching_element_named(task_name)

    def _global_checkpoint_can_be_reached(self, checkpoint_name):
        return self._is_process_state_valid_for_reaching_element_named(checkpoint_name)

    def _local_checkpoint_can_be_reached(self, checkpoint_name):
        there_is_a_task_in_progress = self._there_is_a_task_in_progress()
        if not there_is_a_task_in_progress:
            return False
        task_in_progress_name = self._started_task_name_from_state()
        task_in_progress = self._framework.process().task_specification_named(task_in_progress_name)
        task_in_progress_has_that_checkpoint = any(checkpoint.is_named(checkpoint_name)
                                                   for checkpoint in task_in_progress.checkpoints())
        return task_in_progress_has_that_checkpoint

    def _is_process_state_valid_for_reaching_element_named(self, element_name):
        preceding_elements = (
            self._framework.process().immediately_preceding_elements_for(element_name)
        )
        follows_a_corresponding_finishing_task = any(self._task_had_finished(preceding_element.name())
                                                     for preceding_element in preceding_elements)
        follows_a_corresponding_reached_checkpoint = any(
            self._checkpoint_had_been_reached(preceding_element.name())
            for preceding_element in preceding_elements
        )
        is_starting_element_and_state_is_empty = (
                self._framework.process().is_starting_element(element_name)
                and self._process_state == set()
        )
        return (
                follows_a_corresponding_finishing_task
                or follows_a_corresponding_reached_checkpoint
                or is_starting_element_and_state_is_empty
        )

    def _task_had_started(self, task_name):
        return (task_name + Monitor.TASK_STARTED_SUFFIX) in self._process_state

    def _task_had_finished(self, task_name):
        return (task_name + Monitor.TASK_FINISHED_SUFFIX) in self._process_state

    def _checkpoint_had_been_reached(self, checkpoint_name):
        state_word = checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX
        return state_word in self._process_state

    def _there_is_a_task_in_progress(self):
        return any(
            state_word.endswith(Monitor.TASK_STARTED_SUFFIX)
            for state_word in self._process_state
        )

    def _started_task_name_from_state(self):
        # This method assumes that there is a task in progress.
        for state_word in self._process_state:
            if state_word.endswith(Monitor.TASK_STARTED_SUFFIX):
                return state_word[: state_word.find(Monitor.TASK_STARTED_SUFFIX)]
