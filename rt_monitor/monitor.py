# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import re
import json
import threading
import time
import pika
from pyformlang.finite_automaton import Symbol
import logging

from rt_monitor.errors.framework_errors import FrameworkError
from rt_monitor.framework.framework import Framework
# Create a logger for the monitor component
logger = logging.getLogger(__name__)

from rt_rabbitmq_wrapper.rabbitmq_utility import RabbitMQError
from rt_rabbitmq_wrapper.exchange_types.event.event_dict_codec import EventDictCoDec
from rt_rabbitmq_wrapper.exchange_types.event.event_codec_errors import EventDictError
from rt_rabbitmq_wrapper.exchange_types.verdict.verdict import (
    ProcessVerdict,
    TaskStartedVerdict,
    TaskFinishedVerdict,
    CheckpointReachedVerdict
)
from rt_rabbitmq_wrapper.exchange_types.verdict.verdict_dict_codec import VerdictDictCoDec

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
from rt_monitor.errors.monitor_errors import (
    MonitorError,
    UndeclaredVariableError,
    TaskDoesNotExistError,
    CheckpointDoesNotExistError,
    ComponentDoesNotExistError,
    ComponentError
)
from rt_monitor import rabbitmq_server_connections
from rt_monitor.framework.clock import Clock
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.evaluator import Evaluator
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator


# Errors:
# -1: Framework error
class Monitor(threading.Thread):
    def __init__(self, spec_file, signal_flags):
        super().__init__()
        # Analysis framework
        try:
            self._framework = Framework.framework_from_file(spec_file)
        except FrameworkError:
            logger.critical(f"Error creating framework.")
            raise MonitorError()
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
        logger.info(f"Monitor created.")

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
        # Start receiving events from the RabbitMQ server
        logger.info(f"Start receiving events from queue {rabbitmq_server_connections.rabbitmq_event_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_event_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.port}.")
        # Start sending analysis results to the RabbitMQ server with timeout handling for message reception
        logger.info(f"Start sending analysis results to exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
        # Sets the initial state in the event automata
        self._current_state = self._framework.process().dfa().start_state
        # initialize last_message_time for testing timeout
        last_message_time = time.time()
        start_time_epoch = time.time()
        number_of_events = 0
        # Control variables
        poison_received = False
        completed = False
        stop = False
        abort = False
        while not poison_received and not completed and not stop and not abort:
            # Handle SIGINT
            if self._signal_flags['stop']:
                logger.info("SIGINT received. Stopping the event reception process.")
                stop = True
            # Handle SIGTSTP
            if self._signal_flags['pause']:
                logger.info("SIGTSTP received. Pausing the event reception process.")
                while self._signal_flags['pause'] and not self._signal_flags['stop']:
                    time.sleep(1)  # Efficiently wait for signals
                if self._signal_flags['stop']:
                    logger.info("SIGINT received. Stopping the event reception process.")
                    stop = True
                if not self._signal_flags['pause']:
                    logger.info("SIGTSTP received. Resuming the event reception process.")
            # Timeout handling for message reception
            if 0 < config.timeout < (time.time() - last_message_time):
                abort = True
            # Process event only if temination has not been decided
            if not stop and not abort:
                # Get event from RabbitMQ
                try:
                    method, properties, body = rabbitmq_server_connections.rabbitmq_event_server_connection.get_message()
                except RabbitMQError:
                    logger.critical(f"Error receiving event from queue {rabbitmq_server_connections.rabbitmq_event_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_event_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.port}.")
                    exit(-2)
                if method:  # Message exists
                    # ACK the message from RabbitMQ
                    try:
                        rabbitmq_server_connections.rabbitmq_event_server_connection.ack_message(method.delivery_tag)
                    except RabbitMQError:
                        logger.critical(f"Error sending ack to exchange {rabbitmq_server_connections.rabbitmq_event_server_connection.exchange} at the RabbitMQ event server at {rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.port}.")
                        exit(-2)
                    # Process message
                    if properties.headers and properties.headers.get('termination'):
                        # Poison pill received
                        logger.info(f"Poison pill received from queue {rabbitmq_server_connections.rabbitmq_event_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_event_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.port}.")
                        poison_received = True
                    else:
                        last_message_time = time.time()
                        # Event received
                        event_dict = json.loads(body.decode())
                        try:
                            event = EventDictCoDec.from_dict(event_dict)
                        except EventDictError:
                            logger.critical(f"Error building event from dict: [ {event_dict} ].")
                            abort = True
                        else:
                            logger.debug(f"Received event: {event_dict}")
                            # Process event.
                            try:
                                is_a_valid_report = event.process_with(self)
                            except EXCEPTIONS as f:
                                logger.error(f"Event [ {event_dict} ] produced an error: {f}.")
                                abort = True
                            else:
                                # TODO: Note that the stop policy is decoupled from the validity of the property, thus
                                #  True does not necessarily mean that the analysis of the property is true itself, but
                                #  only that the process should not stop. This ambiguity between the interpretation of
                                #  the variable "is_a_valid_report" and the return value of the function
                                #  _is_property_true should be eliminated in the near future in order to avoid
                                #  misunderstandings.
                                if not is_a_valid_report:
                                    completed = True
                                # Only increment number_of_events is it is a valid event (rules out poisson pill)
                                number_of_events += 1
        # Stop receiving messages from the RabbitMQ server
        logger.info(f"Stop receiving events from queue {rabbitmq_server_connections.rabbitmq_event_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_event_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_event_server_connection.server_info.port}.")
        # Close connection to the RabbitMQ events server if it exists
        #rabbitmq_server_connections.rabbitmq_event_server_connection.close()
        # Send poison pill with the results exchange to the RabbitMQ server
        try:
            rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                '',
                pika.BasicProperties(
                    delivery_mode=2,
                    headers={'termination': True}
                )
            )
        except RabbitMQError:
            logger.critical(f"Error sending poison pill to exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
            exit(-2)
        else:
            logger.info(f"Poison pill sent to exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
        # Stop publishing results to the RabbitMQ server
        logger.info(f"Stop sending verdicts to exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
        # Close connection to the RabbitMQ results log server if it exists
        #rabbitmq_server_connections.rabbitmq_result_log_server_connection.close()
        # Logging the reason for stoping the verification process to the RabbitMQ server
        if poison_received:
            logger.info(f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process COMPLETED, poison pill received.")
        elif completed:
            logger.info(f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process COMPLETED, applied stop policy.")
        elif stop:
            logger.info(f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, SIGINT received.")
        elif abort:
            logger.info(f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, message reception timeout reached ({time.time()-last_message_time} secs.).")
        else:
            logger.info(f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, unknown reason.")

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()
        task_time = task_started_event.timestamp()
        if task_name not in self._framework.process().tasks():
            logger.error(f"Task {task_name} does not exist.")
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
            verdict = TaskStartedVerdict(
                task_time,
                task_name,
                ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            print(verdict_dict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = TaskStartedVerdict(
                task_time,
                task_name,
                ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of preconditions
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
        task_time = task_finished_event.timestamp()
        if task_name not in self._framework.process().tasks():
            logger.error(f"Task {task_name} does not exist.")
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
            verdict = TaskFinishedVerdict(
                task_time,
                task_name,
                ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = TaskFinishedVerdict(
                task_time,
                task_name,
                ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of posconditions
            task_specification = self._framework.process().tasks()[task_name]
            postconditions_are_met = self._are_all_properties_true(
                task_finished_event.timestamp(),
                task_specification.postconditions(),
            )
            self._current_state = destinations[0]
            return postconditions_are_met

    # Raises: CheckpointDoesNotExistError
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()
        checkpoint_time = checkpoint_reached_event.timestamp()
        if checkpoint_name not in self._framework.process().checkpoints():
            logger.error(f"Checkpoint [ {checkpoint_name} ] does not exist.")
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
            verdict = CheckpointReachedVerdict(
                checkpoint_time,
                checkpoint_name,
                ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = CheckpointReachedVerdict(
                checkpoint_time,
                checkpoint_name,
                ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'verdict'}
                    )
                )
            except RabbitMQError:
                logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.server_info.port}.")
                exit(-2)
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of properties
            checkpoint_specification = self._framework.process().checkpoints()[checkpoint_name]
            checkpoint_conditions_are_met = self._are_all_properties_true(
                checkpoint_reached_event.timestamp(),
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
            logger.error(f"Variable [ {variable_name} ] was not declared.")
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
            logger.error(f"Component [ {component_name} ] does not exist.")
            raise ComponentDoesNotExistError()
        component = self._framework.components()[component_name]
        try:
            component.process_high_level_call(component_data)
        except FunctionNotImplementedError as e:
            logger.error(f"Function [ {e.function_name()} ] is not implemented for component [ {component_name} ].")
            raise ComponentError()
        return True

    # Raises: ClockError()
    def process_clock_start(self, clock_start_event):
        clock_name = clock_start_event.clock_name()
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].start(clock_start_event.timestamp())
        except ClockWasAlreadyStartedError:
            logger.error(f"Clock [ {clock_name} ] was already started.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_pause(self, clock_pause_event):
        clock_name = clock_pause_event.clock_name()
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].pause(clock_pause_event.timestamp())
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasAlreadyPausedError:
            logger.error(f"Clock [ {clock_name} ] was already paused.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_resume(self, clock_resume_event):
        clock_name = clock_resume_event.clock_name()
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].resume(clock_resume_event.timestamp())
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasNotPausedError:
            logger.error(f"Clock [ {clock_name} ] was not paused.")
            raise ClockError()
        return True

    # Raises: ClockError()
    def process_clock_reset(self, clock_reset_event):
        clock_name = clock_reset_event.clock_name()
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].reset(clock_reset_event.timestamp())
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
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
            logger.error(f"Error evaluating formula [ {logic_property.name()} ]")
            raise BuildSpecificationError()
        # TODO: Note that the stop policy is decoupled from the validity of the property, thus True does not
        #  necessarily mean that the analysis of the property is true itself, but only that the process should not stop.
        #  This ambiguity between the interpretation of the variable "is_a_valid_report" in lines 212 and 218 and the
        #  return value of this function should be eliminated in the near future in order to avoid misunderstandings.
        match config.stop:
            case "on_might_fail":
                return not (evaluation_result == PropertyEvaluator.PropertyEvaluationResult.FAILED or evaluation_result == PropertyEvaluator.PropertyEvaluationResult.MIGHT_FAIL)
            case "on_fail":
                return not evaluation_result == PropertyEvaluator.PropertyEvaluationResult.FAILED
            case "dont":
                return True
            case _:  # This case cannot happen
                pass
