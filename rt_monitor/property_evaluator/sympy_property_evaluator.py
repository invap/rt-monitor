# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import time
import pika
import logging
# Create a logger for the sympy property evaluator component
logger = logging.getLogger(__name__)

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError,
    EvaluationError, UnsupportedSymPyVariableTypeError
)
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator
from rt_monitor import rabbitmq_server_connections


class SymPyPropertyEvaluator(PropertyEvaluator):
    def __init__(self, components, execution_state, timed_state):
        super().__init__(components, execution_state, timed_state)

    # Raises: EvaluationError()
    def eval(self, now, prop):
        initial_build_time = time.time()
        try:
            spec = self._build_spec(prop, now)
        except BuildSpecificationError:
            logger.error(f"Building specification for property [ {prop.name()} ] error.")
            raise EvaluationError()
        end_build_time = time.time()
        filename = prop.name()
        initial_analysis_time = time.time()
        locs = {}
        exec(spec, globals(), locs)
        # The formula is checked to be either true or false
        result = locs['result']
        end_analysis_time = time.time()
        match result:
            case True:
                # If the formula is true, then the prop of interest passed.
                # Publish log entry at RabbitMQ server
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.channel.basic_publish(
                    exchange=rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange,
                    routing_key='',
                    body=f"Property: {prop.name()} - Timestamp: {now} - Analysis: PASSED - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.",
                    properties=pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'log_entry'}
                    )
                )
                logger.debug(f"Sent log entry: Property: {prop.name()} - Timestamp: {now} - Analysis: PASSED - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.")
            case False:
                # If the formula is false, then the prop of interest failed.
                # Publish log entry at RabbitMQ server
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.channel.basic_publish(
                    exchange=rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange,
                    routing_key='',
                    body=f"Property: {prop.name()} - Timestamp: {now} - Analysis: FAILED - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.",
                    properties=pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'log_entry'}
                    )
                )
                logger.debug(f"Sent log entry: Property: {prop.name()} - Timestamp: {now} - Analysis: FAILED - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.")
        if result == False:
            # Output counterexample as a py program
            spec_filename = filename + "@" + str(now) + ".py"
            # Publish counterexample at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    spec,
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'counterexample', 'filename': spec_filename}
                    )
                )
            except RabbitMQError:
                logger.critical(
                    f"Error sending log entry to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.port}.")
                exit(-2)
            else:
                logger.debug(f"Sent counterexample: Property: {prop.name()} - Timestamp: {now}.")
            return PropertyEvaluator.PropertyEvaluationResult.FAILED
        else:
            return PropertyEvaluator.PropertyEvaluationResult.PASSED

    # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            declarations = self._build_variable_declarations(prop)
            assumptions = self._build_assumptions(prop, now)
            spec = (f"from sympy import Symbol\n" +
                    f"{"".join([decl + "\n" for decl in declarations])}\n" +
                    f"{prop.declarations()}\n\n"
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"result = {prop.formula()}\n")
            return spec
        except NoValueAssignedToVariableError:
            pass
        except UnboundVariablesError:
            pass
        except ClockWasNotStartedError:
            pass
        raise BuildSpecificationError()

    # Raises: UnsupportedSymPyVariableType()
    @staticmethod
    # TODO: implement the use of arrays for sympy programs
    def _build_declaration(variable, variable_type):
        match variable_type:
            case "Bool":
                return f"{variable} = Symbol('{variable}')"
            case "Int":
                return f"{variable} = Symbol('{variable}', integer=True)"
            case "Real":
                return f"{variable} = Symbol('{variable}', real=True)"
            case _:
                logger.error(f"Variable type [ {variable_type} ] of variable [ {variable} ] unsupported.")
                raise UnsupportedSymPyVariableTypeError()

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    # TODO: implement the use of arrays for sympy programs
    def _build_assumption(variable, variable_value):
        assumption = ""
        # Check whether the variable has a value assigned.
        if not isinstance(variable_value, NoValue):
            # The variable has a value assigned.
            assumption = f"{variable} = {variable_value}"
        return assumption

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logger.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        return f"{variable} = {clock.get_time(now)}"
