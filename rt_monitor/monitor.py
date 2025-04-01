# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import re
import threading

from pyformlang.finite_automaton import Symbol

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
    UndeclaredVariableError,
    TaskDoesNotExistError,
    CheckpointDoesNotExistError,
    ComponentDoesNotExistError,
    ComponentError
)
from logging_configuration import LoggingLevel
from framework.clock import Clock
from reporting.event_decoder import EventDecoder
from novalue import NoValue
from property_evaluator.evaluator import Evaluator


class Monitor(threading.Thread):

    def __init__(self, framework, reports_map):
        super().__init__()
        # Analysis framework
        self._framework = framework
        self._current_state = self._framework.process().dfa().start_state
        # Event reports map
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
        # (i.e., self._framework.process().get_variables()[variable][0]) {State|Component|Clock}
        # self._framework.process().variables()[variable][1] is the variable SMT-Lib type.
        for variable in self._framework.process().variables():
            match self._framework.process().variables()[variable][0]:
                case "State":
                    if "Array" in self._framework.process().variables()[variable][1]:
                        self._execution_state[variable] = (self._framework.process().variables()[variable][1], {})
                    else:
                        self._execution_state[variable] = (self._framework.process().variables()[variable][1], NoValue)
                case "Component":
                    # There is nothing to do here; the existence of the variables mentioned in the process in any of
                    # the declared components is checked at the momento of creation of the framework.
                    pass
                case "Clock":
                    self._timed_state[variable] = (
                        self._framework.process().variables()[variable][1], Clock(variable)
                    )
                case _:
                    # There is nothing to do here; variables have already been checked for being of one of the right
                    # types when building the analysis framework.
                    pass
        # Build formula evaluator
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

    def stop_components(self):
        self._framework.stop_components()

    # Raises: AbortRun()
    def run(self):
        is_a_valid_report = True
        abort = False
        for line in self._reports_map["main"]:
            # Decode next event.
            try:
                decoded_event = EventDecoder.decode(line.strip())
            except InvalidEvent as e:
                logging.critical(f"Invalid event [ {e.event().serialized()} ].")
                abort = True
                break
            else:
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
                # Evaluation related exceptions.
                except BuildSpecificationError:
                    logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                # Execution state related exceptions.
                except UndeclaredVariableError:
                    logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                # Clock related exceptions.
                except ClockError:
                    logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                except UndeclaredClockError:
                    logging.error(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                # Task related exceptions.
                except TaskDoesNotExistError:
                    logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                # Checkpoint related exceptions.
                except CheckpointDoesNotExistError:
                    logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                # Component related exceptions.
                except ComponentDoesNotExistError:
                    logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
                except ComponentError:
                    logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error.")
                    abort = True
                    break
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
        if abort:
            logging.critical(f"Runtime verification process ABORTED.")
        else:
            if self._stop_event.is_set():
                if not is_a_valid_report:
                    logging.log(LoggingLevel.ANALYSIS, "Verification completed UNSUCCESSFULLY.")
                else:
                    logging.log(LoggingLevel.ANALYSIS, "Verification completed SUCCESSFULLY.")

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        if not self._framework.process().task_exists(task_name):
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can start only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_started_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"task_started_{task_name}"))
        # As the automaton is deterministic the lenght of destination should be either 0 or 1.
        # assert(len(destinations) <= 1)
        if destinations == []:
            return False
        else:
            task_specification = self._framework.process().task_specification_named(task_name)
            preconditions_are_met = self._are_all_properties_satisfied(
                task_started_event.time(),
                task_specification.preconditions(),
            )
            self._current_state = destinations[0]
            return preconditions_are_met
        #

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()
        if not self._framework.process().task_exists(task_name):
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can finish only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_finished_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"task_finished_{task_name}"))
        # As the automaton is deterministic the lenght of destination should be either 0 or 1.
        assert(len(destinations) <= 1)
        if destinations == []:
            return False
        else:
            task_specification = self._framework.process().task_specification_named(task_name)
            postconditions_are_met = self._are_all_properties_satisfied(
                task_finished_event.time(),
                task_specification.postconditions(),
            )
            self._current_state = destinations[0]
            return postconditions_are_met

    # Raises: CheckpointDoesNotExistError
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        if not self._framework.process().global_checkpoint_exists(checkpoint_name) and not self._framework.process().local_checkpoint_exists(checkpoint_name):
            logging.error(f"Checkpoint [ {checkpoint_name} ] does not exist.")
            raise CheckpointDoesNotExistError()
        # A checkpoint named checkpoint_name can be reached only if the DFA of the process of the analysis
        # framework (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"checkpoint_reached_{checkpoint_name}"; this is equivalent to test
        # whether the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"checkpoint_reached_{checkpoint_name}"))
        # As the automaton is deterministic the lenght of destination should be either 0 or 1.
        assert(len(destinations) <= 1)
        if destinations == []:
            return False
        else:
            if self._framework.process().global_checkpoint_exists(checkpoint_name):
                checkpoint_specification = self._framework.process().global_checkpoint_named(checkpoint_name)
            else:
                checkpoint_specification = self._framework.process().local_checkpoint_named(checkpoint_name)
            checkpoint_conditions_are_met = self._are_all_properties_satisfied(
                checkpoint_reached_event.time(),
                checkpoint_specification.properties(),
            )
            self._current_state = destinations[0]
            return checkpoint_conditions_are_met

    # Raises: UndeclaredVariableError()
    def process_variable_value_assigned(self, variable_value_assigned_event):
        split_variable_name = re.split(r'(?=\[)', variable_value_assigned_event.variable_name(), maxsplit=1)
        variable_name = split_variable_name[0]
        if len(split_variable_name) == 1:
            array = False
        else:
            array = True
            variable_loc = split_variable_name[1]
        variable_value = variable_value_assigned_event.variable_value()
        if variable_name not in self._execution_state:
            logging.error(f"Variable [ {variable_name} ] was not declared.")
            raise UndeclaredVariableError()
        if array:
            array_values = self._execution_state[variable_name][1]
            array_values[variable_loc] = variable_value
        else:
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

    # Propagates: BuildSpecificationError() from _is_property_satisfied
    def _are_all_properties_satisfied(self, event_time, logic_properties):
        neg_properties_sat = False
        for logic_property in logic_properties:
            if neg_properties_sat:
                break
            neg_properties_sat = self._is_property_satisfied(event_time, logic_property)
        return not neg_properties_sat

    # Propagates: BuildSpecificationError()
    def _is_property_satisfied(self, event_time, logic_property):
        logging.log(LoggingLevel.ANALYSIS, f"Checking property {logic_property.name()}...")
        try:
            negation_is_sat = self._evaluator.eval(logic_property, event_time)
        except BuildSpecificationError:
            logging.error(f"Error evaluating formula [ {logic_property.name()} ]")
            raise BuildSpecificationError()
        if not negation_is_sat:
            logging.log(LoggingLevel.ANALYSIS, f"Property {logic_property.name()} PASSED")
        else:
            logging.log(LoggingLevel.ANALYSIS, f"Property {logic_property.name()} FAILED")
        return negation_is_sat

