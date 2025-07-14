# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import re
import signal
import threading
import time
from pyformlang.finite_automaton import Symbol

from rt_monitor.config import config
from rt_monitor.errors.clock_errors import (
    ClockError,
    UndeclaredClockError,
    ClockWasAlreadyStartedError,
    ClockWasNotStartedError,
    ClockWasAlreadyPausedError,
    ClockWasNotPausedError
)
from rt_monitor.errors.component_errors import FunctionNotImplementedError
from rt_monitor.errors.evaluator_errors import BuildSpecificationError
from rt_monitor.errors.event_decoder_errors import InvalidEvent
from rt_monitor.errors.monitor_errors import (
    UndeclaredVariableError,
    TaskDoesNotExistError,
    CheckpointDoesNotExistError,
    ComponentDoesNotExistError,
    ComponentError
)
from rt_monitor.rabbitmq_server_config import rabbitmq_server_config
from rt_monitor.rabbitmq_utility import (
    setup_rabbitmq
)
from rt_monitor.logging_configuration import LoggingLevel
from rt_monitor.framework.clock import Clock
from rt_monitor.reporting.event_decoder import EventDecoder
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.evaluator import Evaluator
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator

# Errors:
# -3: RabbitMQ server setup error

class Monitor(threading.Thread):
    ERROR_EXCEPTIONS = (
        BuildSpecificationError,
        UndeclaredVariableError,
        ClockError,
        UndeclaredClockError
    )
    CRITICAL_EXCEPTIONS = (
        TaskDoesNotExistError,
        CheckpointDoesNotExistError,
        ComponentDoesNotExistError,
        ComponentError
    )

    def __init__(self, framework, signal_flags):
        super().__init__()
        # Analysis framework
        self._framework = framework
        # Signaling flags
        self._signal_flags = signal_flags
        # State
        self._current_state = None
        self._execution_state = {}
        self._timed_state = {}
        # Build the state dictionary discarding the variable class
        # (i.e., self._framework.process().get_variables()[variable][0]) {State|Component|Clock}
        # self._framework.process().variables()[variable][1] is the variable SMT-Lib type.
        for variable in self._framework.process().variables():
            match self._framework.process().variables()[variable][0]:
                case "State":
                    if "Array" in self._framework.process().variables()[variable][1]:
                        # Array data is stored as a dictionary whose keys are the position of in the array.
                        self._execution_state[variable] = (self._framework.process().variables()[variable][1], {})
                    else:
                        self._execution_state[variable] = (self._framework.process().variables()[variable][1], NoValue())
                case "Component":
                    # There is nothing to do here; the existence of the variables mentioned in the process in any of
                    # the declared components is checked at the moment of the creation of the framework.
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
            self._execution_state,
            self._timed_state
        )

    # Raises:
    def run(self):
        last_message_time = time.time()
        # Control variables
        poison_received = False
        stop = False
        abort = False
        # Setup RabbitMQ server
        logging.info(f"Establishing connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        connection, channel, queue_name = setup_rabbitmq()
        logging.info(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} established.")
        # Start getting events from the RabbitMQ server with timeout handling for message reception
        logging.info(f"Start getting events from RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        is_a_valid_report = True
        # Initialize process state for the analysis
        self._current_state = self._framework.process().dfa().start_state
        while not poison_received and not self._signal_flags['stop']:
            # Handle SIGINT
            if self._signal_flags['stop']:
                logging.info("SIGINT received. Stopping the event acquisition process.")
                poison_received = True
            # Handle SIGTSTP
            if self._signal_flags['pause']:
                logging.info("SIGTSTP received. Pausing the event acquisition process.")
                while self._signal_flags['pause'] and not self._signal_flags['stop']:
                    signal.pause()  # Efficiently wait for signals
                if self._signal_flags['stop']:
                    logging.info("SIGINT received. Stopping the event acquisition process.")
                    poison_received = True
                logging.info("SIGTSTP received. Resuming the event acquisition process.")
            # Get event from RabbitMQ
            method, properties, body = channel.basic_get(queue=queue_name, auto_ack=False)
            if method:  # Message exists
                # Process message
                if properties.headers and properties.headers.get('termination'):
                    # Poison pill received
                    logging.log(LoggingLevel.EVENT, f"Poison pill received.")
                    stop = True
                    abort = False
                    poison_received = True
                else:
                    last_message_time = time.time()
                    # Decode the next event.
                    event = body.decode().rstrip('\n\r')
                    try:
                        decoded_event = EventDecoder.decode(event.split(","))
                    except InvalidEvent as f:
                        logging.critical(f"Invalid event [ {f.event().serialized()} ].")
                        stop = True
                        abort = True
                        poison_received = True
                    else:
                        logging.log(LoggingLevel.EVENT, f"Processing: {decoded_event.serialized()}")
                        # Process event.
                        try:
                            is_a_valid_report = decoded_event.process_with(self)
                        except Monitor.ERROR_EXCEPTIONS as f:
                            logging.error(f"Event [ {decoded_event.serialized()} ] produced an error: {f}.")
                            stop = True
                            abort = True
                            poison_received = True
                        except Monitor.CRITICAL_EXCEPTIONS as f:
                            logging.critical(f"Event [ {decoded_event.serialized()} ] produced an error: {f}.")
                            stop = True
                            abort = True
                            poison_received = True
                        else:
                            # Action if the event caused the verification to fail.
                            if not is_a_valid_report:
                                logging.info(
                                    f"The following event caused the verification to fail: "
                                    f"[ {decoded_event.serialized()} ]"
                                )
                                stop = True
                                poison_received = True
                # ACK the message
                channel.basic_ack(method.delivery_tag)
            if stop:
                if abort:
                    logging.critical("Runtime verification process ABORTED.")
                else:
                    if is_a_valid_report:
                        logging.log(LoggingLevel.ANALYSIS, "Verification completed SUCCESSFULLY.")
                    else:
                        logging.log(LoggingLevel.ANALYSIS, "Verification completed UNSUCCESSFULLY.")
                poison_received = True
            # Timeout handling for message reception
            if 0 < config.timeout < (time.time() - last_message_time):
                logging.info(f"No event received for {config.timeout} seconds. Timeout reached.")
                poison_received = True
        # Close connection if it exists
        if connection and connection.is_open:
            try:
                connection.close()
                logging.info(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} closed.")
            except Exception as e:
                logging.error(f"Error closing connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}: {e}.")
        logging.info(f"Stop getting events from RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        if task_name not in self._framework.process().tasks():
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can start only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_started_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"task_started_{task_name}"))
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        # assert(len(destinations) <= 1)
        if destinations == []:
            logging.log(LoggingLevel.ANALYSIS, f"Task [ {task_name} ] cannot start.")
            return False
        else:
            task_specification = self._framework.process().tasks()[task_name]
            preconditions_are_met = self._are_all_properties_true(
                task_started_event.time(),
                task_specification.preconditions(),
            )
            self._current_state = destinations[0]
            return preconditions_are_met

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()
        if task_name not in self._framework.process().tasks():
            logging.error(f"Task [ {task_name} ] does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can finish only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_finished_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"task_finished_{task_name}"))
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        assert(len(destinations) <= 1)
        if destinations == []:
            logging.log(LoggingLevel.ANALYSIS, f"Task [ {task_name} ] cannot finish.")
            return False
        else:
            task_specification = self._framework.process().tasks()[task_name]
            postconditions_are_met = self._are_all_properties_true(
                task_finished_event.time(),
                task_specification.postconditions(),
            )
            self._current_state = destinations[0]
            return postconditions_are_met

    # Raises: CheckpointDoesNotExistError
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        if checkpoint_name not in self._framework.process().checkpoints():
            logging.error(f"Checkpoint [ {checkpoint_name} ] does not exist.")
            raise CheckpointDoesNotExistError()
        # A checkpoint named checkpoint_name can be reached only if the DFA of the process of the analysis
        # framework (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"checkpoint_reached_{checkpoint_name}"; this is equivalent to test
        # whether the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(self._current_state, Symbol(f"checkpoint_reached_{checkpoint_name}"))
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        # assert(len(destinations) <= 1)
        if destinations == []:
            logging.log(LoggingLevel.ANALYSIS, f"Checkpoint [ {checkpoint_name} ] is unreachable.")
            return False
        else:
            checkpoint_specification = self._framework.process().checkpoints()[checkpoint_name]
            checkpoint_conditions_are_met = self._are_all_properties_true(
                checkpoint_reached_event.time(),
                checkpoint_specification.properties(),
            )
            self._current_state = destinations[0]
        return checkpoint_conditions_are_met

    # Raises: UndeclaredVariableError()
    def process_variable_value_assigned(self, variable_value_assigned_event):
        # Determine whether the variable being assigned is a component of an array.
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
    def _are_all_properties_true(self, event_time, logic_properties):
        property_is_true = True
        for logic_property in logic_properties:
            if not property_is_true:
                break
            property_is_true = self._is_property_true(event_time, self._framework.process().properties()[logic_property])
        return property_is_true

    # Propagates: BuildSpecificationError()
    def _is_property_true(self, event_time, logic_property):
        try:
            evaluation_result = self._evaluator.eval(event_time, logic_property)
        except BuildSpecificationError:
            logging.error(f"Error evaluating formula [ {logic_property.name()} ]")
            raise BuildSpecificationError()
        return evaluation_result == PropertyEvaluator.PropertyEvaluationResult.PASSED

