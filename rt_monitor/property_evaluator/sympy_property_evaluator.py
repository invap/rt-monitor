# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import json
import time
import pika
import logging
# Create a logger for the sympy property evaluator component
logger = logging.getLogger(__name__)

from rt_rabbitmq_wrapper.rabbitmq_utility import RabbitMQError
from rt_rabbitmq_wrapper.exchange_types.verdict.verdict import SymPyVerdict
from rt_rabbitmq_wrapper.exchange_types.verdict.verdict_dict_codec import VerdictDictCoDec
from rt_rabbitmq_wrapper.exchange_types.specification.specification import SymPySpecification
from rt_rabbitmq_wrapper.exchange_types.specification.specification_dict_codec import SpecificationDictCoDec

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError,
    UnsupportedSymPyVariableTypeError,
    EvaluationError
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
                # Publish verdict at RabbitMQ server
                verdict = SymPyVerdict(
                    now,
                    prop.name(),
                    SymPyVerdict.VERDICT.PASS,
                    end_build_time - initial_build_time,
                    end_analysis_time - initial_analysis_time
                )
                verdict_dict = VerdictDictCoDec.to_dict(verdict)
                try:
                    rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                        json.dumps(verdict_dict),
                        pika.BasicProperties(
                            delivery_mode=2,  # Persistent message
                            headers={'type': 'verdict'}
                        )
                    )
                except RabbitMQError:
                    logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.port}.")
                    exit(-2)
                else:
                    logger.debug(f"Sent verdict: [ {verdict} ].")
            case False:
                # If the formula is false, then the prop of interest failed.
                # Publish verdict at RabbitMQ server
                verdict = SymPyVerdict(
                    now,
                    prop.name(),
                    SymPyVerdict.VERDICT.FAIL,
                    end_build_time - initial_build_time,
                    end_analysis_time - initial_analysis_time
                )
                verdict_dict = VerdictDictCoDec.to_dict(verdict)
                try:
                    rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                        json.dumps(verdict_dict),
                        pika.BasicProperties(
                            delivery_mode=2,  # Persistent message
                            headers={'type': 'verdict'}
                        )
                    )
                except RabbitMQError:
                    logger.critical(f"Error sending verdict to the exchange {rabbitmq_server_connections.rabbitmq_result_log_server_connection.exchange} at the RabbitMQ server at {rabbitmq_server_connections.rabbitmq_result_log_server_connection.host}:{rabbitmq_server_connections.rabbitmq_result_log_server_connection.port}.")
                    exit(-2)
                else:
                    logger.debug(f"Sent verdict: [ {verdict} ].")
        if result == False:
            # Output counterexample as a py program
            specification_dict = SpecificationDictCoDec.to_dict(
                SymPySpecification(prop.name(), now, spec)
            )
            # Publish counterexample at RabbitMQ server
            try:
                rabbitmq_server_connections.rabbitmq_result_log_server_connection.publish_message(
                    json.dumps(specification_dict),
                    pika.BasicProperties(
                        delivery_mode=2,  # Persistent message
                        headers={'type': 'counterexample'}
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
