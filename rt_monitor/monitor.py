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

# Create a logger for the monitor component
logger = logging.getLogger(__name__)

from rt_monitor.errors.framework_errors import FrameworkError
from rt_monitor.framework.framework import Framework
from rt_monitor.config import config
from rt_monitor.errors.clock_errors import (
    ClockError,
    UndeclaredClockError,
    ClockWasAlreadyStartedError,
    ClockWasNotStartedError,
    ClockWasAlreadyPausedError,
    ClockWasNotPausedError,
)
from rt_monitor.errors.component_errors import FunctionNotImplementedError
from rt_monitor.errors.evaluator_errors import BuildSpecificationError
from rt_monitor.errors.monitor_errors import (
    MonitorError,
    UndeclaredVariableError,
    TaskDoesNotExistError,
    CheckpointDoesNotExistError,
    ComponentDoesNotExistError,
    ComponentError,
)
from rt_monitor import rabbitmq_server_connections
from rt_monitor.framework.clock import Clock
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.evaluator import Evaluator
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator

from rt_rabbitmq_wrapper.exchange_types.verdict.process_verdict import ProcessVerdict
from rt_rabbitmq_wrapper.exchange_types.verdict.task_started_verdict import TaskStartedVerdict
from rt_rabbitmq_wrapper.exchange_types.verdict.task_finished_verdict import TaskFinishedVerdict
from rt_rabbitmq_wrapper.exchange_types.verdict.checkpoint_reached_verdict import CheckpointReachedVerdict
from rt_rabbitmq_wrapper.rabbitmq_utility import RabbitMQError
from rt_rabbitmq_wrapper.exchange_types.event.event_dict_codec import EventDictCoDec
from rt_rabbitmq_wrapper.exchange_types.event.event_codec_errors import EventDictError
from rt_rabbitmq_wrapper.exchange_types.verdict.verdict_dict_codec import AnalysisVerdict, PyVerdict, SMT2Verdict, SymPyVerdict, VerdictDictCoDec, VerdictDictError, VerdictTypeError, VerdictTypeError


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
                    self._timed_state[variable] = (self._framework.process().variables()[variable][1], Clock(variable))
                case _:
                    # There is nothing to do here; variables have already been checked for being of one of the right
                    # types when building the analysis framework.
                    pass
        # Build formula evaluator
        self._evaluator = Evaluator(self._framework.components(), self._execution_state, self._timed_state)
        logger.info(f"Monitor created.")

    # Raises: MonitorError
    def run(self):
        EXCEPTIONS = (
            BuildSpecificationError,
            UndeclaredVariableError,
            ClockError,
            UndeclaredClockError,
            TaskDoesNotExistError,
            CheckpointDoesNotExistError,
            ComponentDoesNotExistError,
            ComponentError,
        )
        # Start receiving events from the RabbitMQ server
        logger.info(
            f"Start receiving events from queue {rabbitmq_server_connections.rabbitmq_events_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_events_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.port}."
        )
        # Start receiving analysis results from the RabbitMQ server with timeout handling for message reception
        logger.info(
            f"Start receiving analysis results from queue {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.port}."
        )
        # Start sending analysis results to the RabbitMQ server with timeout handling for message reception
        logger.info(
            f"Start sending analysis results to exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
        )
        # Sets the initial state in the event automata
        self._current_state = self._framework.process().dfa().start_state
        # initialize last_message_time for testing timeout
        last_message_time = time.time()
        start_time_epoch = time.time()
        number_of_events = 0
        # Control variables
        control = {
            "poison_received": False,
            "verdict_stop": False,
            "timeout_stop": False,
            "signal_stop": False
        }
        while not control['signal_stop'] and not control['poison_received'] and not control['timeout_stop'] and not control['verdict_stop']:
            # Check for signals and handle them accordingly
            Monitor._handle_signals(control, self._signal_flags)
            # Check for termination due to timeout
            Monitor._check_timeout(control, last_message_time)
            # Check for termination due to negative verdict reception
            Monitor._check_termination_by_verdict(control)
            # Process event only if termination has not been decided
            if not control['signal_stop'] and not control['timeout_stop'] and not control['verdict_stop']:
                # Get event from RabbitMQ server
                try:
                    method, properties, body = (rabbitmq_server_connections.rabbitmq_events_server_connection.get_message())
                except RabbitMQError:
                    logger.critical(f"Error receiving event from queue {rabbitmq_server_connections.rabbitmq_events_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_events_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.port}.")
                    raise MonitorError()
                if method:  # Message exists
                    # ACK the message from RabbitMQ
                    try:
                        rabbitmq_server_connections.rabbitmq_events_server_connection.ack_message(method.delivery_tag)
                    except RabbitMQError:
                        logger.critical(f"Error sending ack to exchange {rabbitmq_server_connections.rabbitmq_events_server_connection.exchange} at the RabbitMQ event server at {rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.port}.")
                        raise MonitorError()
                    # Process message
                    if properties.headers and properties.headers.get("termination"):
                        # Poison pill received
                        logger.info(f"Poison pill received from queue {rabbitmq_server_connections.rabbitmq_events_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_events_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.port}.")
                        control["poison_received"] = True
                    else:
                        last_message_time = time.time()
                        # Event received
                        event_dict = json.loads(body.decode())
                        try:
                            event = EventDictCoDec.from_dict(event_dict)
                        except EventDictError:
                            logger.critical(f"Error building event from dict: [ {event_dict} ].")
                            raise MonitorError()
                        else:
                            logger.debug(f"Received event: {event_dict}")
                            # Process event.
                            try:
                                event.process_with(self)
                            except EXCEPTIONS as f:
                                logger.error(f"Event [ {event_dict} ] produced an error: {f}.")
                                raise MonitorError()
                            else:
                                # Only increment number_of_events is it is a valid event (rules out poisson pill)
                                number_of_events += 1
        # Stop receiving messages from the RabbitMQ server
        logger.info(
            f"Stop receiving events from queue {rabbitmq_server_connections.rabbitmq_events_server_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_events_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_events_server_connection.server_info.port}."
        )
        # Stop receiving messages from the RabbitMQ server
        logger.info(
            f"Stop receiving analysis results from queue {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.port}."
        )
        # Send poison pill with the results exchange to the RabbitMQ server
        try:
            rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                "", pika.BasicProperties(delivery_mode=2, headers={"termination": True})
            )
        except RabbitMQError:
            logger.critical(
                f"Error sending poison pill to exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
            )
            raise MonitorError()
        else:
            logger.info(
                f"Poison pill sent to exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
            )
        # Stop publishing results to the RabbitMQ server
        logger.info(
            f"Stop sending analysis results to exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
        )
        # Close connection to the RabbitMQ analysis results server if it exists
        # rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.close()
        # Logging the reason for stoping the verification process to the RabbitMQ server
        if control["poison_received"]:
            logger.info(
                f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process COMPLETED, poison pill received."
            )
        elif control["signal_stop"]:
            logger.info(
                f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, SIGINT received."
            )
        elif control["timeout_stop"]:
            logger.info(
                f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, timeout reached."
            )
        elif control["verdict_stop"]:
            logger.info(
                f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, termination by verdict."
            )
        else:
            logger.info(
                f"Events processed: {number_of_events} - Time (secs.): {time.time()-start_time_epoch:.3f} - Process STOPPED, unknown reason."
            )

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_started(self, task_started_event):
        task_name = task_started_event.name
        task_time = task_started_event.timestamp
        if task_name not in self._framework.process().tasks():
            logger.error(f"Task {task_name} does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can start only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_started_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(
            self._current_state, Symbol(f"task_started_{task_name}")
        )
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        # assert(len(destinations) <= 1)
        if destinations == []:
            verdict = TaskStartedVerdict(
                task_time, task_name, ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            print(verdict_dict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = TaskStartedVerdict(
                task_time, task_name, ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of preconditions
            task_specification = self._framework.process().tasks()[task_name]
            self._are_properties_satisfied(task_time, task_specification.preconditions())
            self._current_state = destinations[0]

    # Raises: TaskDoesNotExistError()
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name
        task_time = task_finished_event.timestamp
        if task_name not in self._framework.process().tasks():
            logger.error(f"Task {task_name} does not exist.")
            raise TaskDoesNotExistError()
        # A task named task_name can finish only if the DFA of the process of the analysis framework
        # (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"task_finished_{task_name}"; this is equivalent to test whether
        # the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(
            self._current_state, Symbol(f"task_finished_{task_name}")
        )
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        assert len(destinations) <= 1
        if destinations == []:
            verdict = TaskFinishedVerdict(
                task_time, task_name, ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = TaskFinishedVerdict(
                task_time, task_name, ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of posconditions
            task_specification = self._framework.process().tasks()[task_name]
            self._are_properties_satisfied(task_finished_event.timestamp, task_specification.postconditions())
            self._current_state = destinations[0]

    # Raises: CheckpointDoesNotExistError
    # Propagates: BuildSpecificationError() from _are_all_properties_satisfied
    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name
        checkpoint_time = checkpoint_reached_event.timestamp
        if checkpoint_name not in self._framework.process().checkpoints():
            logger.error(f"Checkpoint [ {checkpoint_name} ] does not exist.")
            raise CheckpointDoesNotExistError()
        # A checkpoint named checkpoint_name can be reached only if the DFA of the process of the analysis
        # framework (i.e., self._framework.process().dfa()) has an outgoing transition from the current state
        # (self._current_state) labelled f"checkpoint_reached_{checkpoint_name}"; this is equivalent to test
        # whether the list of destinations from the current state through transitions labelled with that symbol
        # is not empty.
        destinations = self._framework.process().dfa()(
            self._current_state, Symbol(f"checkpoint_reached_{checkpoint_name}")
        )
        # As the automaton is deterministic, the length of destination should be either 0 or 1.
        # assert(len(destinations) <= 1)
        if destinations == []:
            verdict = CheckpointReachedVerdict(
                checkpoint_time, checkpoint_name, ProcessVerdict.VERDICT.FAIL
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            return False
        else:
            verdict = CheckpointReachedVerdict(
                checkpoint_time, checkpoint_name, ProcessVerdict.VERDICT.PASS
            )
            verdict_dict = VerdictDictCoDec.to_dict(verdict)
            # Publish verdict at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.publish_message(
                    json.dumps(verdict_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={"type": "verdict"},
                    ),
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.server_info.port}."
                )
                raise MonitorError()
            logger.debug(f"Sent verdict: [ {verdict} ].")
            # Analysis of properties
            checkpoint_specification = self._framework.process().checkpoints()[
                checkpoint_name
            ]
            self._are_properties_satisfied(checkpoint_reached_event.timestamp, checkpoint_specification.properties())
            self._current_state = destinations[0]

    # Raises: UndeclaredVariableError()
    def process_variable_value_assigned(self, variable_value_assigned_event):
        # Determine whether the variable being assigned is a component of an array.
        split_variable_name = re.split(
            r"(?=\[)", variable_value_assigned_event.variable_name, maxsplit=1
        )
        variable_name = split_variable_name[0]
        if len(split_variable_name) == 1:
            array = False
        else:
            array = True
            variable_loc = split_variable_name[1]
        variable_value = variable_value_assigned_event.variable_value
        if variable_name not in self._execution_state:
            logger.error(f"Variable [ {variable_name} ] was not declared.")
            raise UndeclaredVariableError()
        if array:
            array_values = self._execution_state[variable_name][1]
            array_values[variable_loc] = variable_value
        else:
            self._execution_state[variable_name] = (
                self._execution_state[variable_name][0],
                variable_value,
            )

    # Raises: ComponentDoesNotExistError(), ComponentError()
    def process_component_event(self, component_event):
        component_data = component_event.data
        component_name = component_event.component_name
        if component_name not in self._framework.components():
            logger.error(f"Component [ {component_name} ] does not exist.")
            raise ComponentDoesNotExistError()
        component = self._framework.components()[component_name]
        try:
            component.process_high_level_call(component_data)
        except FunctionNotImplementedError as e:
            logger.error(
                f"Function [ {e.function_name()} ] is not implemented for component [ {component_name} ]."
            )
            raise ComponentError()

    # Raises: ClockError()
    def process_clock_start(self, clock_start_event):
        clock_name = clock_start_event.clock_name
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].start(clock_start_event.timestamp)
        except ClockWasAlreadyStartedError:
            logger.error(f"Clock [ {clock_name} ] was already started.")
            raise ClockError()

    # Raises: ClockError()
    def process_clock_pause(self, clock_pause_event):
        clock_name = clock_pause_event.clock_name
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].pause(clock_pause_event.timestamp)
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasAlreadyPausedError:
            logger.error(f"Clock [ {clock_name} ] was already paused.")
            raise ClockError()

    # Raises: ClockError()
    def process_clock_resume(self, clock_resume_event):
        clock_name = clock_resume_event.clock_name
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].resume(clock_resume_event.timestamp)
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()
        except ClockWasNotPausedError:
            logger.error(f"Clock [ {clock_name} ] was not paused.")
            raise ClockError()

    # Raises: ClockError()
    def process_clock_reset(self, clock_reset_event):
        clock_name = clock_reset_event.clock_name
        if clock_name not in self._timed_state:
            logger.error(f"Clock [ {clock_name} ] was not declared.")
            raise UndeclaredClockError()
        try:
            self._timed_state[clock_name][1].reset(clock_reset_event.timestamp)
        except ClockWasNotStartedError:
            logger.error(f"Clock [ {clock_name} ] was not started.")
            raise ClockError()

    # Raises: BuildSpecificationError()
    def _are_properties_satisfied(self, event_time, logic_properties):
        for logic_property in logic_properties:
            try:
                self._evaluator.eval(event_time, self._framework.process().properties()[logic_property])
            except BuildSpecificationError:
                logger.error(f"Error evaluating formula [ {logic_property} ]")
                raise BuildSpecificationError()

    # Functions used to check termination of the monitoring process by signals, timeout and verdict 
    # reception. They update the control dictionary with the corresponding flags to indicate whether 
    # the monitoring process should be stopped or not.
    @staticmethod
    def _handle_signals(control, signal_flags):
        # Handle SIGINT
        if signal_flags["stop"]:
            logger.info("SIGINT received. Stopping the event reception process.")
            control["signal_stop"] = True
        # Handle SIGTSTP
        if signal_flags["pause"]:
            logger.info("SIGTSTP received. Pausing the event reception process.")
            while signal_flags["pause"] and not signal_flags["stop"]:
                time.sleep(1)  # Efficiently wait for signals
            if signal_flags["stop"]:
                logger.info("SIGINT received. Stopping the event reception process.")
                control["signal_stop"] = True
            if not signal_flags["pause"]:
                logger.info("SIGTSTP received. Resuming the event reception process.")
                control["signal_stop"] = False
        control["signal_stop"] = False

    @staticmethod
    def _check_timeout(control, last_message_time):
        if 0 < config.timeout < (time.time() - last_message_time):
            control["timeout_stop"] = True

    @staticmethod
    def _check_termination_by_verdict(control):
        # Get analysis results from RabbitMQ server
        try:
            method, properties, body = (rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.get_message())
        except RabbitMQError:
            logger.critical(f"Error receiving analysis results from queue {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.queue_name} - exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.port}.")
            raise MonitorError()
        if method:  # Message exists
            # ACK the message from RabbitMQ
            try:
                rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.ack_message(method.delivery_tag)
            except RabbitMQError:
                logger.critical(f"Error sending ack to exchange {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.exchange} at the RabbitMQ event server at {rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.host}:{rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.server_info.port}.")
                raise MonitorError()
            # Process message
            if (properties.headers and properties.headers.get("type") and properties.headers.get("type") == "verdict"):
                # Verdict received
                verdict_dict = json.loads(body.decode())
                try:
                    verdict = VerdictDictCoDec.from_dict(verdict_dict)
                except VerdictDictError:
                    logger.critical(f"Error parsing verdict dictionary: {verdict_dict}.")
                    raise MonitorError()
                except VerdictTypeError:
                    logger.critical(f"Error building dictionary from verdict: {verdict}.")
                    raise MonitorError()
                else:
                    control["verdict_stop"] = Monitor._check_termination_by_verdict_type(verdict)
            else:
                # Not a verdict message, ignore it
                control["verdict_stop"] = False
        else:
            # No message exists
            control["verdict_stop"] = False

    @staticmethod
    def _check_termination_by_verdict_type(verdict):
        if isinstance(verdict, ProcessVerdict):
            return Monitor._check_termination_by_process_verdict(verdict)
        elif isinstance(verdict, AnalysisVerdict):
            return Monitor._check_termination_by_analysis_verdict(verdict)
        else:
            logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
            raise MonitorError()

    @staticmethod
    def _check_termination_by_process_verdict(verdict: ProcessVerdict):
        match verdict.verdict:
            case ProcessVerdict.VERDICT.FAIL:
                logger.debug(f"Verdict [ {verdict} ] received, process should stop according to the stop policy.")
                # Note that for process verdicts, the process should stop if a FAIL verdict is received 
                # independently of the stop policy.
                return True
            case ProcessVerdict.VERDICT.PASS:
                logger.debug(f"Verdict [ {verdict} ] received, process should not stop according to the stop policy.")
                return False
            case _:
                logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
                raise MonitorError()

    @staticmethod
    def _check_termination_by_analysis_verdict(verdict: AnalysisVerdict):
        if isinstance(verdict, PyVerdict):
            return Monitor._check_termination_by_py_verdict(verdict)
        elif isinstance(verdict, SymPyVerdict):
            return Monitor._check_termination_by_sympy_verdict(verdict)
        elif isinstance(verdict, SMT2Verdict):
            return Monitor._check_termination_by_smt2_verdict(verdict)
        else:
            logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
            raise MonitorError()
        
    @staticmethod
    def _check_termination_by_py_verdict(verdict: PyVerdict):
        match verdict.verdict:
            case PyVerdict.VERDICT.FAIL:
                logger.debug(f"Verdict [ {verdict} ] received, process should stop according to the stop policy.")
                return False if config.stop == "dont" else True
            case PyVerdict.VERDICT.PASS:
                logger.debug(f"Verdict [ {verdict} ] received, process should not stop according to the stop policy.")
                return False
            case _:
                logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
                raise MonitorError()

    @staticmethod
    def _check_termination_by_sympy_verdict(verdict: SymPyVerdict):
        match verdict.verdict:
            case SymPyVerdict.VERDICT.FAIL:
                logger.debug(f"Verdict [ {verdict} ] received, process should stop according to the stop policy.")
                return False if config.stop == "dont" else True
            case SymPyVerdict.VERDICT.PASS:
                logger.debug(f"Verdict [ {verdict} ] received, process should not stop according to the stop policy.")
                return False
            case _:
                logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
                raise MonitorError()

    @staticmethod
    def _check_termination_by_smt2_verdict(verdict: SMT2Verdict):
        match verdict.verdict:
            case SMT2Verdict.VERDICT.FAIL:
                logger.debug(f"Verdict [ {verdict} ] received, process should stop according to the stop policy.")
                return False if config.stop == "dont" else True
            case SMT2Verdict.VERDICT.PASS:
                logger.debug(f"Verdict [ {verdict} ] received, process should not stop according to the stop policy.")
                return False
            case SMT2Verdict.VERDICT.MIGHT_FAIL:
                logger.debug(f"Verdict [ {verdict} ] received, process should stop according to the stop policy.")
                return False if config.stop == "dont" or config.stop == "on_fail" else True
            case _:
                logger.critical(f"Verdict [ {verdict} ] is not of a valid type.")
                raise MonitorError()

