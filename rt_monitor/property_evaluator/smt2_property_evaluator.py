# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import time
import pika
import numpy as np
from z3 import z3
import logging
# Create a logger for the smt2 property evaluator component
logger = logging.getLogger(__name__)

from rt_monitor.errors.clock_errors import ClockWasNotStartedError
from rt_monitor.errors.evaluator_errors import (
    NoValueAssignedToVariableError,
    UnboundVariablesError,
    BuildSpecificationError, EvaluationError
)
from rt_monitor.logging_configuration import LoggingLevel
from rt_monitor.monitor import AnalysisStatistics
from rt_monitor.novalue import NoValue
from rt_monitor.property_evaluator.property_evaluator import PropertyEvaluator
from rt_monitor.rabbitmq_utility.rabbitmq_server_connections import rabbitmq_log_server_connection


class SMT2PropertyEvaluator(PropertyEvaluator):
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
        temp_solver = z3.Solver()
        temp_solver.from_string(spec)
        # The negation of the formula is checked for satisfiability
        result = temp_solver.check()
        end_analysis_time = time.time()
        match result:
            case z3.unsat:
                # If the negation of the formula is unsatisfiable, then the prop_dict of interest passed.
                # Publish log entry at RabbitMQ server
                rabbitmq_log_server_connection.channel.basic_publish(
                    exchange=rabbitmq_log_server_connection.exchange,
                    routing_key='log_entry',
                    body=f"Property: {prop.name()} - Timestamp: {now} - Analysis: [ PASSED ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.",
                    properties=pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
                logger.log(LoggingLevel.DEBUG, f"Sent log entry: Property: {prop.name()} - Timestamp: {now} - Analysis: [ PASSED ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.")
                AnalysisStatistics.passed()
            case z3.sat:
                # If the negation of the formula is satisfiable, then the prop_dict of interest failed.
                # Publish log entry at RabbitMQ server
                rabbitmq_log_server_connection.channel.basic_publish(
                    exchange=rabbitmq_log_server_connection.exchange,
                    routing_key='log_entry',
                    body=f"Property: {prop.name()} - Timestamp: {now} - Analysis: [ FAILED ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.",
                    properties=pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
                logger.log(LoggingLevel.DEBUG, f"Sent log entry: Property: {prop.name()} - Timestamp: {now} - Analysis: [ FAILED ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.")
                AnalysisStatistics.failed()
            case z3.unknown:
                # If the negation of the formula is unknown, then the prop_dict of interest is not guarantied to pass.
                # Publish log entry at RabbitMQ server
                rabbitmq_log_server_connection.channel.basic_publish(
                    exchange=rabbitmq_log_server_connection.exchange,
                    routing_key='log_entry',
                    body=f"Property: {prop.name()} - Timestamp: {now} - Analysis: [ MIGHT FAIL ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.",
                    properties=pika.BasicProperties(
                        delivery_mode=2  # Persistent message
                    )
                )
                logger.log(LoggingLevel.DEBUG, f"Sent log entry: Property: {prop.name()} - Timestamp: {now} - Analysis: [ MIGHT FAIL ] - Spec. build time (secs.): {end_build_time - initial_build_time:.3f} - Analysis time (secs.): {end_analysis_time - initial_analysis_time:.3f}.")
                AnalysisStatistics.might_fail()
        if result == z3.sat or result == z3.unknown:
            # Output counterexample as smt2 specification
            spec_filename = filename + "@" + str(now) + ".smt2"
            spec_file = open(spec_filename, "w")
            spec_file.write(spec)
            spec_file.close()
            logger.info(f"Specification dumped: [ {spec_filename} ]")
            if result == z3.sat:
                return PropertyEvaluator.PropertyEvaluationResult.FAILED
            else:
                return PropertyEvaluator.PropertyEvaluationResult.MIGHT_FAIL
        else:
            return PropertyEvaluator.PropertyEvaluationResult.PASSED

        # Raises: BuildSpecificationError()
    def _build_spec(self, prop, now):
        try:
            var_declarations = self._build_variable_declarations(prop)
            assumptions = self._build_assumptions(prop, now)
            spec = (f"{"".join([decl + "\n" for decl in var_declarations])}\n" +
                    f"{prop.declarations()}\n\n"
                    f"{"".join([ass + "\n" for ass in assumptions])}\n" +
                    f"(assert (not {prop.formula()}))\n")
            return spec
        except NoValueAssignedToVariableError:
            pass
        except UnboundVariablesError:
            pass
        except ClockWasNotStartedError():
            pass
        raise BuildSpecificationError()

    # Raises: UnsupportedSMT2VariableTypeError()
    @staticmethod
    def _build_declaration(variable, variable_type):
        # As types are declared in the input files using SMT2Lib standard there is nothing to do here
        return f"(declare-const {variable} {variable_type})"

    # Raises: NoValueAssignedToVariableError()
    @staticmethod
    def _build_assumption(variable, variable_value):
        assumption = ""
        if isinstance(variable_value, np.ndarray):
            # The variable is of type np.ndarray, mainly used for implementing the internal structure
            # of digital twins
            # We assume that the instance has assigned values to all its components
            assumption = "(assert (and \n"
            var_value_shape = variable_value.shape
            current = [0] * (len(var_value_shape) + 1)
            while SMT2PropertyEvaluator._more(current):
                value = SMT2PropertyEvaluator._get_value(variable_value, current)
                selector = SMT2PropertyEvaluator._build_selector(variable, current)
                assumption += f"(= {selector} {value})\n"
                SMT2PropertyEvaluator._plus_one(var_value_shape, current)
            assumption += "))"
        elif isinstance(variable_value, dict):
            # The variable is of type dict, used for monitoring arrays whose dimension is unknown by the monitor
            if not all([isinstance(x, NoValue) for x in variable_value.values()]):
                # The instance has assigned values to some its components
                assumption = "(assert \n"
                assumption += "(and \n"
                for key in variable_value:
                    if not isinstance(variable_value[key], NoValue):
                        # key if of the form [i0][i1]...[in]
                        split_key = key.removeprefix("[").removesuffix("]").split("][")
                        assumption += "(= "
                        for _i in range(0, len(split_key)):
                            assumption += f"(select "
                        assumption += f"{variable} "
                        for i in split_key:
                            assumption += f"{i}) "
                        assumption += f"{variable_value[key]})\n"
                assumption += ")\n)\n"
        else:
            # The variable is of one of the basic types supported expressed with a string
            if not isinstance(variable_value, NoValue):
                assumption = f"(assert (= {variable} {variable_value}))\n"
        return assumption

    # Raises: ClockWasNotStartedError()
    @staticmethod
    def _build_time_assumption(variable, clock, now):
        # Check whether the clock has been started.
        if not clock.has_started():
            logger.error(f"Clock [ {clock.name()} ] was not started.")
            raise ClockWasNotStartedError()
        # The clock has been started.
        assumption = f"(assert (= {variable} {clock.get_time(now)}))\n"
        return assumption

    @staticmethod
    def _build_selector(var_name, current):
        select = var_name
        for position in range(1, len(current)):
            select = f"(select {select} {current[position]})"
        return select
