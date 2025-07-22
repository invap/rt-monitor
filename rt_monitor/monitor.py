# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import re
import threading
import time
import pika
from pyformlang.finite_automaton import Symbol

from rt_monitor.analysis_statistics import AnalysisStatistics
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
from rt_monitor.rabbitmq_server_configs import (
    rabbitmq_server_config,
    rabbitmq_event_exchange_config,
    rabbitmq_log_exchange_config
)
from rt_monitor.rabbitmq_server_connections import rabbitmq_event_server_connection, rabbitmq_log_server_connection
from rt_monitor.rabbitmq_utility import (
    RabbitMQError,
    get_message,
    ack_message,
    publish_message,
    connect_to_server,
    connect_to_channel_exchange,
    declare_queue
)
from rt_monitor.logging_configuration import LoggingLevel
from rt_monitor.framework.clock import Clock
from rt_monitor.reporting.event_decoder import EventDecoder
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.evaluator import Evaluator
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


# Errors:
# -2: RabbitMQ server setup error

class Monitor(threading.Thread):
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
        EXCEPTIONS = (
            BuildSpecificationError,
            UndeclaredVariableError,
            ClockError,
            UndeclaredClockError,
            TaskDoesNotExistError,
            CheckpointDoesNotExistError,
            ComponentDoesNotExistError,
            ComponentError
        )

        last_message_time = time.time()
        # Control variables
        poison_received = False
        stop = False
        abort = False
        # Set up the connection to the RabbitMQ connection to server
        try:
            connection = connect_to_server(rabbitmq_server_config)
        except RabbitMQError:
            logging.critical(f"Error setting up the connection to the RabbitMQ server.")
            exit(-2)
        # Set up the RabbitMQ channel and exchange for events with the RabbitMQ server
        try:
            event_channel = connect_to_channel_exchange(rabbitmq_server_config, rabbitmq_event_exchange_config, connection)
        except RabbitMQError:
            logging.critical(f"Error setting up the channel and exchange at the RabbitMQ server.")
            exit(-2)
        # Set up the RabbitMQ queue and routing key for events with the RabbitMQ server
        try:
            event_queue_name = declare_queue(rabbitmq_server_config, rabbitmq_event_exchange_config, event_channel, 'events')
        except RabbitMQError:
            logging.critical(f"Error setting up the channel and exchange at the RabbitMQ server.")
            exit(-2)
        # Start getting events from the RabbitMQ server
        logging.info(f"Start getting events from queue {event_queue_name} - exchange {rabbitmq_event_exchange_config.exchange} at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        # Set up connection for events with the RabbitMQ server
        rabbitmq_event_server_connection.connection = connection
        rabbitmq_event_server_connection.channel = event_channel
        rabbitmq_event_server_connection.exchange = rabbitmq_event_exchange_config.exchange
        rabbitmq_event_server_connection.queue_name = event_queue_name
        # Set up the RabbitMQ channel and exchange for logging with the RabbitMQ server
        try:
            log_channel = connect_to_channel_exchange(rabbitmq_server_config, rabbitmq_log_exchange_config, connection)
        except RabbitMQError:
            logging.critical(f"Error setting up the channel and exchange at the RabbitMQ server.")
            exit(-2)
        # Start sending log entries to the RabbitMQ server with timeout handling for message reception
        logging.info(f"Start sending log entries to the exchange {rabbitmq_log_exchange_config.exchange} at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        # Set up connection for events with the RabbitMQ server
        rabbitmq_log_server_connection.connection = connection
        rabbitmq_log_server_connection.channel = log_channel
        rabbitmq_log_server_connection.exchange = rabbitmq_log_exchange_config.exchange
        # Initialize process state for the analysis
        self._current_state = self._framework.process().dfa().start_state
        while not poison_received and not self._signal_flags['stop']:
            # Handle SIGINT
            if self._signal_flags['stop']:
                logging.info("SIGINT received. Stopping the event acquisition process.")
                break
            # Handle SIGTSTP
            if self._signal_flags['pause']:
                logging.info("SIGTSTP received. Pausing the event acquisition process.")
                while self._signal_flags['pause'] and not self._signal_flags['stop']:
                    time.sleep(1)  # Efficiently wait for signals
                if self._signal_flags['stop']:
                    logging.info("SIGINT received. Stopping the event acquisition process.")
                    break
                logging.info("SIGTSTP received. Resuming the event acquisition process.")
            # Timeout handling for message reception
            if 0 < config.timeout < (time.time() - last_message_time):
                logging.info(f"No event received for {config.timeout} seconds. Timeout reached.")
                break
            # Get event from RabbitMQ
            try:
                method, properties, body = get_message(rabbitmq_event_server_connection)
            except RabbitMQError:
                logging.critical(f"Error getting message from RabbitMQ server.")
                exit(-2)
            if method:  # Message exists
                # Process message
                if properties.headers and properties.headers.get('termination'):
                    # Poison pill received
                    logging.info(f"Poison pill received.")
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
                        exit(-3)
                    else:
                        logging.log(LoggingLevel.DEBUG, f"Received event: {decoded_event.serialized()}")
                        AnalysisStatistics.event()
                        # Process event.
                        try:
                            is_a_valid_report = decoded_event.process_with(self)
                        except EXCEPTIONS as f:
                            logging.error(f"Event [ {decoded_event.serialized()} ] produced an error: {f}.")
                            exit(-3)
                        else:
                            # Action if the event caused the verification to fail.
                            if not is_a_valid_report:
                                stop = True
                                poison_received = True
                # ACK the message
                try:
                    ack_message(rabbitmq_event_server_connection, method.delivery_tag)
                except RabbitMQError:
                    logging.critical(f"Error acknowledging a message to the RabbitMQ event server.")
                    exit(-2)
            if stop:
                if abort:
                    logging.info("Runtime verification process ABORTED.")
                else:
                    logging.info(f"Runtime verification process COMPLETED.")
                poison_received = True
        # Stop getting events from the RabbitMQ server
        logging.info(f"Stop getting events from the RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        # Log analysis statistics
        Monitor.log_analysis_statistics()
        # Send poison pill to the RabbitMQ logging server
        try:
            publish_message(
                rabbitmq_log_server_connection,
                'log_entries',
                '',
                pika.BasicProperties(
                    delivery_mode=2,
                    headers={'termination': True}
                )
            )
        except RabbitMQError:
            logging.info("Error sending poison pill to the RabbitMQ logging server.")
            exit(-2)
        else:
            logging.info("Poison pill sent.")
        # Stop publishing log entries to the RabbitMQ server
        logging.info(f"Stop publishing log entries to the RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        # Close connection to the RabbitMQ logging server if it exists
        if connection and connection.is_open:
            try:
                connection.close()
                logging.info(f"Connection to the RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} closed.")
            except Exception:
                logging.error(f"Error closing the logging connection to the RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        task_time = task_started_event.time()
        if task_name not in self._framework.process().tasks():
            logging.error(f"Task {task_name} does not exist.")
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
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Task {task_name} cannot start at timestamp {task_time} [ FAIL ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Sent log entry: Task {task_name} cannot start at timestamp {task_time} [ FAIL ].")
            return False
        else:
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Task {task_name} started at timestamp {task_time} [ PASSED ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Sent log entry: Task {task_name} started at timestamp {task_time} [ PASSED ].")
            task_specification = self._framework.process().tasks()[task_name]
            preconditions_are_met = self._are_all_properties_true(
                task_time,
                task_specification.preconditions(),
            )
            self._current_state = destinations[0]
            return preconditions_are_met

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()
        task_time = task_finished_event.time()
        if task_name not in self._framework.process().tasks():
            logging.error(f"Task {task_name} does not exist.")
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
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Task {task_name} cannot finish at timestamp {task_time} [ FAIL ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Sent log entry: Task {task_name} cannot finish at timestamp {task_time} [ FAIL ].")
            return False
        else:
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Task {task_name} finished at timestamp {task_time} [ PASSED ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Sent log entry: Task {task_name} finished at timestamp {task_time} [ PASSED ].")
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
        checkpoint_time = checkpoint_reached_event.time()
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
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Checkpoint {checkpoint_name} is unreachable at timestamp {checkpoint_time} [ FAIL ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Checkpoint {checkpoint_name} is unreachable at timestamp {checkpoint_time} [ FAIL ].")
            return False
        else:
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"Checkpoint {checkpoint_name} reached at timestamp {checkpoint_time} [ PASSED ].",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"Checkpoint {checkpoint_name} reached at timestamp {checkpoint_time} [ PASSED ].")
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
            logging.error(f"Function [ {e.function_name()} ] is not implemented for component [ {component_name} ].")
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
        match config.stop:
            case "on_might_fail":
                return not (evaluation_result == PropertyEvaluator.PropertyEvaluationResult.FAILED or evaluation_result == PropertyEvaluator.PropertyEvaluationResult.MIGHT_FAIL)
            case "on_fail":
                return not evaluation_result == PropertyEvaluator.PropertyEvaluationResult.FAILED
            case "dont":
                return True
            case _:  # This case cannot happen
                pass

    @staticmethod
    def log_analysis_statistics():
        # Publish log entry at RabbitMQ server
        try:
            publish_message(
                rabbitmq_log_server_connection,
                'log_entries',
                "--------------- Analysis Statistics ---------------",
                pika.BasicProperties(
                    delivery_mode=2  # Persistent message
                )
            )
        except RabbitMQError:
            logging.info("Error sending log entry to the RabbitMQ server.")
            exit(-2)
        logging.debug(f"Sent log entry: --------------- Analysis Statistics ---------------")
        # Publish log entry at RabbitMQ server
        try:
            publish_message(
                rabbitmq_log_server_connection,
                'log_entries',
                f"Processed events: {AnalysisStatistics.events}.",
                pika.BasicProperties(
                    delivery_mode=2  # Persistent message
                )
            )
        except RabbitMQError:
            logging.info("Error sending log entry to the RabbitMQ server.")
            exit(-2)
        logging.debug(f"Processed events: {AnalysisStatistics.events}.")
        # Compute the total number of properties
        total_props = AnalysisStatistics.passed_props + AnalysisStatistics.might_fail_props + AnalysisStatistics.failed_props
        # Publish log entry at RabbitMQ server
        try:
            publish_message(
                rabbitmq_log_server_connection,
                'log_entries',
                f"Analyzed properties: {total_props}.",
                pika.BasicProperties(
                    delivery_mode=2  # Persistent message
                )
            )
        except RabbitMQError:
            logging.info("Error sending log entry to the RabbitMQ server.")
            exit(-2)
        logging.debug(f"Analyzed properties: {total_props}.")
        if total_props > 0:
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"PASSED properties: {AnalysisStatistics.passed_props} ({AnalysisStatistics.passed_props * 100 / total_props:.2f}%).",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"PASSED properties: {AnalysisStatistics.passed_props} ({AnalysisStatistics.passed_props * 100 / total_props:.2f}%).")
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"MIGHT FAIL properties: {AnalysisStatistics.might_fail_props} ({AnalysisStatistics.might_fail_props * 100 / total_props:.2f}%).",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"MIGHT FAIL properties: {AnalysisStatistics.might_fail_props} ({AnalysisStatistics.might_fail_props * 100 / total_props:.2f}%).")
            # Publish log entry at RabbitMQ server
            try:
                publish_message(
                    rabbitmq_log_server_connection,
                    'log_entries',
                    f"FAILED properties: {AnalysisStatistics.failed_props} ({AnalysisStatistics.failed_props * 100 / total_props:.2f}%).",
                    pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
            except RabbitMQError:
                logging.info("Error sending log entry to the RabbitMQ server.")
                exit(-2)
            logging.debug(f"FAILED properties: {AnalysisStatistics.failed_props} ({AnalysisStatistics.failed_props * 100 / total_props:.2f}%).")
