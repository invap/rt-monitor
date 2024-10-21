# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys

from toml.decoder import TomlDecodeError

from errors.errors import AnalysisFailed, FormulaError, FunctionNotImplemented, FrameworkFileError, ReportsFileError
from errors.event_errors import EventError, InvalidEvent
from errors.framework_errors import TaskDoesNotExist, CheckpointDoesNotExist, ComponentDoesNotExist
from errors.variable_errors import UndeclaredComponentVariable, UnknownVariableClass, UndeclaredVariable
from framework.process.framework import Framework
from logging_configuration import LoggingLevel, LoggingDestination
from framework.clock import Clock
from errors.clock_errors import (
    UndeclaredClock,
    ClockWasNotStarted,
    ClockWasAlreadyPaused,
    ClockWasNotPaused,
    ClockWasAlreadyStarted
)
from reporting.event.event import Event
from reporting.event_decoder import EventDecoder
from novalue import NoValue
from property_evaluator.evaluator import Evaluator


class Monitor:
    PROCESS_IDLE_STATE = "process_idle"
    PROCESS_FINISHED = "process_finished"

    TASK_STARTED_SUFFIX = "_started"
    TASK_FINISHED_SUFFIX = "_finished"
    CHECKPOINT_REACHED_SUFFIX = "_reached"

    def __init__(self, framework, reports_map):
        # Analysis framework
        self._framework = framework
        # revent reports
        self._reports_map = reports_map
        # State
        self._process_state = set()
        self._execution_state = {}
        self._timed_state = {}
        # Building the state dictionary discarding the variable class
        # (i.e., self._framework.process().get_variables()[variable][0]) {State|Component|Clock}.
        for variable in self._framework.process().get_variables():
            match self._framework.process().get_variables()[variable][0]:
                case "State":
                    self._execution_state[variable] = (self._framework.process().get_variables()[variable][1], NoValue)
                case "Component":
                    # check whether all component variables appearing in the formulas in the process
                    if not any([variable in self._framework.components()[component].state() for component in
                                self._framework.components()]):
                        raise UndeclaredComponentVariable(variable)
                case "Clock":
                    self._timed_state[variable] = (
                        self._framework.process().get_variables()[variable][1], Clock(variable)
                    )
                case _:
                    raise UnknownVariableClass(variable, self._framework.process().get_variables()[variable][0])
        # Formula evaluator
        self._evaluator = Evaluator(self._framework.components(), self._process_state, self._execution_state,
                                    self._timed_state)

    @staticmethod
    def new_from_files(logging_destination, logging_level, framework_file, reports_list_file, visual=False):
        # Configure logging
        _set_up_logging()
        _configure_logging_destination(logging_destination)
        _configure_logging_level(logging_level)
        # Build analysis framework
        try:
            framework = Framework(framework_file, visual)
        except TomlDecodeError as e:
            logging.error(f"TOML error in file: {framework_file}, line: {e.lineno}, column: {e.colno} - [ {e.msg} ].")
            raise FrameworkFileError(framework_file)
        except FormulaError as e:
            logging.error(f"Variables in formula [ {e.get_formula()} ] have not been declared.")
            raise FrameworkFileError(framework_file)
        except UndeclaredComponentVariable as e:
            logging.error(f"The variables [ {e.variable_names()} ] is not declared in any component.")
            raise FrameworkFileError(framework_file)
        # Build reports list map
        reports_map = {}
        try:
            file = open(reports_list_file, "r")
        except FileNotFoundError as e:
            logging.error(f"Event reports list file [ {e.filename} ] not found.")
            raise ReportsFileError(reports_list_file)
        try:
            for line in file:
                split_line = line.strip().split(",")
                report_name = split_line[0]
                reports_map[report_name] = open(split_line[1], "r")
        except FileNotFoundError as e:
            logging.error(f"Event report file [ {e.filename} ] not found.")
            raise ReportsFileError(reports_list_file)
        if "main" not in reports_map:
            logging.error(f"Main event report file not found.")
            raise ReportsFileError(reports_list_file)
        # Build monitor
        try:
            return Monitor(framework, reports_map)
        except UnknownVariableClass as e:
            logging.error(
                f"The variable class [ {e.variable_class()} ] of variable [ {e.variable_names()} ] is unknown.")
            raise FrameworkFileError(framework_file)

    def run(self, pause_event=None, stop_event=None, event_processed_callback=None):
        decoded_event = Event(0)
        try:
            is_a_valid_report = True
            for line in self._reports_map["main"]:
                if not is_a_valid_report:
                    break
                Monitor._pause_verification_if_requested(pause_event, stop_event)
                if Monitor._event_was_set(stop_event):
                    break
                decoded_event = EventDecoder.decode(line.strip())
                logging.info(f"Processing: {decoded_event.serialized()}")
                mark = decoded_event.time()
                # Process the events of all self-logged components until time mark
                for component in self._reports_map:
                    if not component == "main":
                        self._framework.components()[component].process_log(self._reports_map[component], mark)
                #
                is_a_valid_report = decoded_event.process_with(self)
                if event_processed_callback is not None:
                    event_processed_callback()
                if not is_a_valid_report:
                    logging.info(
                        f"The following event resulted in an invalid verification: "
                        f"[ {decoded_event.serialized()} ]"
                    )
            if Monitor._event_was_set(stop_event):
                logging.info(f"Verification process STOPPED.")
            elif not is_a_valid_report:
                logging.log(LoggingLevel.PROPERTY_ANALYSIS, "Verification completed UNSUCCESSFULLY.")
            else:
                logging.log(LoggingLevel.PROPERTY_ANALYSIS, "Verification completed SUCCESSFULLY.")
            return is_a_valid_report
        # Clock related exceptions
        except UndeclaredClock as e:
            logging.error(f"Clock [ {e.get_clockname()} ] was not declared.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        except ClockWasAlreadyStarted as e:
            logging.error(f"Clock [ {e.get_clockname()} ] was already started.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        except ClockWasNotStarted as e:
            logging.error(f"Clock [ {e.get_clockname()} ] was not started.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        except ClockWasAlreadyPaused as e:
            logging.error(f"Clock [ {e.get_clockname()} ] was already paused.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        except ClockWasNotPaused as e:
            logging.error(f"Clock [ {e.get_clockname()} ] was not paused.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        # Task related exceptions
        except TaskDoesNotExist as e:
            logging.error(f"Task [ {e.get_task_name()} ] does not exist.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        # Checkpoint related exceptions
        except CheckpointDoesNotExist as e:
            logging.error(f"Checkpoint [ {e.get_checkpoint_name()} ] does not exist.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        # Execution state related exceptions
        except UndeclaredVariable as e:
            logging.error(f"Variable [ {e.variable_names()} ] was not declared.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        # Component related exceptions
        except ComponentDoesNotExist as e:
            logging.error(f"Component [ {e.get_component_name()} ] does not exist.")
            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
        # Events related exceptions
        except EventError as e:
            logging.critical(f"Event [ {e.get_event().serialized()} ] produced an error.")
        except InvalidEvent as e:
            logging.critical(f"Invalid event [ {e.get_event().serialized()} ].")

    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        if not self._framework.process().task_exists(task_name):
            raise TaskDoesNotExist(task_name)
        can_start = self._task_can_start(task_name)
        task_specification = self._framework.process().task_specification_named(task_name)
        try:
            preconditions_are_met = self._are_all_properties_satisfied(
                task_started_event.time(),
                task_specification.preconditions(),
            )
            self._update_process_state_with_started_task(task_started_event)
            return can_start and preconditions_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(task_started_event)

    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()
        if not self._framework.process().task_exists(task_name):
            raise TaskDoesNotExist(task_name)
        had_previously_started = self._task_had_started(task_name)
        task_specification = self._framework.process().task_specification_named(task_name)
        try:
            postconditions_are_met = self._are_all_properties_satisfied(
                task_finished_event.time(),
                task_specification.postconditions(),
            )
            self._update_process_state_with_finished_task(task_finished_event)
            return had_previously_started and postconditions_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(task_finished_event)

    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        if (not self._framework.process().global_checkpoint_exists(checkpoint_name) and
                not self._framework.process().local_checkpoint_exists(checkpoint_name)):
            raise CheckpointDoesNotExist(checkpoint_name)
        else:
            try:
                if self._framework.process().global_checkpoint_exists(checkpoint_name):
                    return self._process_global_checkpoint_reached(checkpoint_reached_event)
                if self._framework.process().local_checkpoint_exists(checkpoint_name):
                    return self._process_local_checkpoint_reached(checkpoint_reached_event)
            except AnalysisFailed:
                logging.critical(f"Analysis FAILED.")
                raise EventError(checkpoint_reached_event)

    def _process_global_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        can_be_reached = self._global_checkpoint_can_be_reached(checkpoint_name)
        checkpoint = self._framework.process().global_checkpoint_named(checkpoint_name)
        properties_are_met = self._are_all_properties_satisfied(checkpoint_reached_event.time(),
                                                                checkpoint.properties())
        self._update_process_state_with_reached_global_checkpoint(checkpoint_reached_event)
        return can_be_reached and properties_are_met

    def _process_local_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        can_be_reached = self._local_checkpoint_can_be_reached(checkpoint_name)
        checkpoint = self._framework.process().local_checkpoint_named(checkpoint_name)
        properties_are_met = self._are_all_properties_satisfied(checkpoint_reached_event.time(),
                                                                checkpoint.properties())
        started_task_name = self._started_task_name_from_state()
        self._update_process_state_with_reached_local_checkpoint(checkpoint_reached_event, started_task_name)
        return can_be_reached and properties_are_met

    def process_variable_value_assigned(self, variable_value_assigned_event):
        variable_name = variable_value_assigned_event.variable_name()
        variable_value = variable_value_assigned_event.variable_value()
        if variable_name not in self._execution_state:
            raise UndeclaredVariable(variable_name)
        self._execution_state[variable_name] = (self._execution_state[variable_name][0], variable_value)
        return True

    def process_component_event(self, component_event):
        component_data = component_event.data()
        component_name = component_event.component_name()
        if component_name not in self._framework.components():
            raise ComponentDoesNotExist(component_name)
        component = self._framework.components()[component_name]
        try:
            component.process_high_level_call(component_data)
        except FunctionNotImplemented as e:
            logging.error(
                f"Function [ {e.get_function_name()} ] is not implemented for component [ {component_name} ]."
            )
            raise EventError(component_event)
        return True

    def process_clock_start(self, clock_start_event):
        clock_name = clock_start_event.clock_name()
        if clock_name not in self._timed_state:
            raise UndeclaredClock(clock_name)
        self._timed_state[clock_name][1].start(clock_start_event.time())
        return True

    def process_clock_pause(self, clock_pause_event):
        clock_name = clock_pause_event.clock_name()
        if clock_name not in self._timed_state:
            raise UndeclaredClock(clock_name)
        self._timed_state[clock_name][1].pause(clock_pause_event.time())
        return True

    def process_clock_resume(self, clock_resume_event):
        clock_name = clock_resume_event.clock_name()
        if clock_name not in self._timed_state:
            raise UndeclaredClock(clock_name)
        self._timed_state[clock_name][1].resume(clock_resume_event.time())
        return True

    def process_clock_reset(self, clock_reset_event):
        clock_name = clock_reset_event.clock_name()
        if clock_name not in self._timed_state:
            raise UndeclaredClock(clock_name)
        self._timed_state[clock_name][1].reset(clock_reset_event.time())
        return True

    def stop_component_monitoring(self):
        for component_name in self._framework.components():
            self._framework.components()[component_name].stop()

    def _update_process_state_with_started_task(self, task_started_event):
        task_name = task_started_event.name()
        self._process_state.clear()
        self._process_state.add(task_name + Monitor.TASK_STARTED_SUFFIX)

    def _update_process_state_with_finished_task(self, task_finished_event):
        task_name = task_finished_event.name()
        self._process_state.clear()
        self._process_state.add(task_name + Monitor.TASK_FINISHED_SUFFIX)

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

    def _is_property_satisfied(self, event_time, logic_property):
        logging.log(LoggingLevel.PROPERTY_ANALYSIS, f"Checking property {logic_property.name()}...")
        try:
            negation_is_sat = self._evaluator.eval(logic_property, event_time)
        except FormulaError as e:
            logging.error(f"Error in formula [ {logic_property.filename()} ]")
            raise e
        if not negation_is_sat:
            logging.log(LoggingLevel.PROPERTY_ANALYSIS, f"Property {logic_property.name()} PASSED")
        else:
            logging.log(LoggingLevel.PROPERTY_ANALYSIS, f"Property {logic_property.name()} FAILED")
        return negation_is_sat

    def _are_all_properties_satisfied(self, event_time, logic_properties):
        neg_properties_sat = False
        for logic_property in logic_properties:
            if neg_properties_sat:
                break
            try:
                neg_properties_sat = self._is_property_satisfied(event_time, logic_property)
            except FormulaError:
                raise AnalysisFailed()
        return not neg_properties_sat

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

    @staticmethod
    def _pause_verification_if_requested(pause_event, stop_event):
        # This is busy waiting. There are better solutions.
        if Monitor._event_was_set(pause_event):
            logging.info(f"Verification paused.")
            while pause_event.is_set():
                if stop_event.is_set():
                    return
            logging.info(f"Verification resumed.")

    @staticmethod
    def _event_was_set(ui_event):
        return ui_event is not None and ui_event.is_set()


def _set_up_logging():
    logging.addLevelName(LoggingLevel.PROPERTY_ANALYSIS, "PROPERTY_ANALYSIS")
    logging.basicConfig(
        stream=sys.stdout,
        level=_default_logging_level(),
        datefmt=_date_logging_format(),
        format=_logging_format(),
        encoding="utf-8",
    )


def _configure_logging_destination(logging_destination):
    logging.getLogger().handlers.clear()
    formatter = logging.Formatter(
        _logging_format(), datefmt=_date_logging_format()
    )
    match logging_destination:
        case LoggingDestination.FILE:
            handler = logging.FileHandler(
                "sandbox/rt-monitor-example-app/log.txt", encoding="utf-8"
            )
        case _:
            handler = logging.StreamHandler(sys.stdout)

    handler.setFormatter(formatter)
    logging.getLogger().addHandler(handler)


def _configure_logging_level(logging_level):
    logging.getLogger().setLevel(logging_level)


def _default_logging_level():
    return LoggingLevel.INFO


def _date_logging_format():
    return "%d/%m/%Y %H:%M:%S"


def _logging_format():
    return "%(asctime)s : [%(name)s:%(levelname)s] - %(message)s"
