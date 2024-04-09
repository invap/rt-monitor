import logging
from collections.abc import Iterable

import z3

from logging_configuration import LoggingLevel
from workflow_runtime_verification.errors import (
    UndeclaredVariable,
    UnboundVariables,
    AlreadyDeclaredVariable,
    NoValueAssignedToVariable,
    NoValue,
    AnalysisFailed,
    CheckpointDoesNotExist,
    TaskDoesNotExist,
    ComponentDoesNotExist,
    FunctionNotImplemented,
    FormulaError,
    EventError,
    AbortRun,
)
from workflow_runtime_verification.reporting.event_decoder import EventDecoder


class Monitor:
    WORKFLOW_IDLE_STATE = "wf_idle"
    WORKFLOW_FINISHED = "wf_finished"

    TASK_STARTED_SUFFIX = "_started"
    TASK_FINISHED_SUFFIX = "_finished"
    CHECKPOINT_REACHED_SUFFIX = "_reached"

    def __init__(self, workflow_specification, component_dictionary):
        self._component_dictionary = component_dictionary
        self._workflow_specification = workflow_specification
        self._workflow_state = set()
        self._execution_state = {}

    def run(
        self,
        event_report_file,
        pause_event=None,
        stop_event=None,
        event_processed_callback=None,
    ):
        try:
            is_a_valid_report = True
            for line in event_report_file:
                if not is_a_valid_report:
                    break

                self._pause_verification_if_requested(pause_event, stop_event)
                if self._event_was_set(stop_event):
                    break

                decoded_event = EventDecoder.decode(line.strip())
                logging.info(f"Processing: {decoded_event.serialized()}")
                is_a_valid_report = decoded_event.process_with(self)

                if event_processed_callback is not None:
                    event_processed_callback()

                if not is_a_valid_report:
                    logging.info(
                        f"The following event resulted in an invalid verification: "
                        f"[ {decoded_event.serialized()} ]"
                    )

            if self._event_was_set(stop_event):
                logging.info(f"Verification process STOPPED.")
            elif not is_a_valid_report:
                self.__class__._log_property_analysis(
                    f"Verification completed UNSUCCESSFULLY."
                )
            else:
                self.__class__._log_property_analysis(
                    f"Verification completed SUCCESSFULLY."
                )

            return is_a_valid_report
        except TaskDoesNotExist as e:
            logging.error(f"Task [ {e.getTaskName()} ] does not exist.")
        except CheckpointDoesNotExist as e:
            logging.error(f"Checkpoint [ {e.getCheckpointName()} ] does not exist.")
        except AlreadyDeclaredVariable as e:
            logging.error(f"Variable [ {e.getVarname()} ] is already declared.")
        except EventError as e:
            logging.critical(f"Event [ {e.getEvent()} ] produced an error.")

        logging.critical(f"Runtime monitoring process ABORTED.")
        raise AbortRun()

    def process_task_started(self, task_started_event):
        task_name = task_started_event.name()

        if not self._workflow_specification.task_exists(task_name):
            raise TaskDoesNotExist(task_name)

        can_start = self._task_can_start(task_name)

        task_specification = self._workflow_specification.task_specification_named(
            task_name
        )
        try:
            preconditions_are_met = self.__class__._are_all_properties_satisfied(
                task_started_event.time(),
                self._execution_state,
                self._component_dictionary,
                task_specification.preconditions(),
            )

            self._update_workflow_state_with_started_task(task_started_event)

            return can_start and preconditions_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(task_started_event)

    def process_task_finished(self, task_finished_event):
        task_name = task_finished_event.name()

        if not self._workflow_specification.task_exists(task_name):
            raise TaskDoesNotExist(task_name)

        had_previously_started = self._task_had_started(task_name)

        task_specification = self._workflow_specification.task_specification_named(
            task_name
        )
        try:
            postconditions_are_met = self.__class__._are_all_properties_satisfied(
                task_finished_event.time(),
                self._execution_state,
                self._component_dictionary,
                task_specification.postconditions(),
            )

            self._update_workflow_state_with_finished_task(task_finished_event)

            return had_previously_started and postconditions_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(task_finished_event)

    def process_declare_variable(self, declare_variable_event):
        variable_name = declare_variable_event.variable_name()
        variable_type = declare_variable_event.variable_type()

        if variable_name in self._execution_state:
            raise AlreadyDeclaredVariable(variable_name)

        self._execution_state[variable_name] = [variable_type, NoValue()]
        return True

    def process_variable_value_assigned(self, variable_value_assigned_event):
        variable_name = variable_value_assigned_event.variable_name()
        variable_value = variable_value_assigned_event.variable_value()

        if variable_name not in self._execution_state:
            raise UndeclaredVariable(variable_name)

        self._execution_state[variable_name] = [
            self._execution_state[variable_name][0],
            variable_value,
        ]
        return True

    def process_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()

        if self._workflow_specification.global_checkpoint_exists(checkpoint_name):
            return self._process_global_checkpoint_reached(checkpoint_reached_event)

        if self._workflow_specification.local_checkpoint_exists(checkpoint_name):
            return self._process_local_checkpoint_reached(checkpoint_reached_event)

        raise CheckpointDoesNotExist(checkpoint_name)

    def process_component_event(self, component_event):
        component_data = component_event.data()
        component_name = component_event.component_name()

        if component_name not in self._component_dictionary:
            raise ComponentDoesNotExist(component_name)

        try:
            component = self._component_dictionary[component_name]
            component.process_high_level_call(component_data)
            return True
        except FunctionNotImplemented as e:
            logging.error(
                f"Function [ {e.getFunctionName()} ] is not implemented for component [ {component_name} ]."
            )
            raise EventError(component_event)

    def stop_component_monitoring(self):
        for component_name in self._component_dictionary:
            self._component_dictionary[component_name].stop()

    def _update_workflow_state_with_started_task(self, task_started_event):
        task_name = task_started_event.name()

        self._workflow_state.clear()
        self._workflow_state.add(task_name + Monitor.TASK_STARTED_SUFFIX)

    def _update_workflow_state_with_finished_task(self, task_finished_event):
        task_name = task_finished_event.name()

        self._workflow_state.clear()
        self._workflow_state.add(task_name + Monitor.TASK_FINISHED_SUFFIX)

    def _update_workflow_state_with_reached_global_checkpoint(
        self, checkpoint_reached_event
    ):
        checkpoint_name = checkpoint_reached_event.name()

        self._workflow_state = {
            state_word
            for state_word in self._workflow_state
            if not state_word.endswith(Monitor.CHECKPOINT_REACHED_SUFFIX)
        }
        self._workflow_state.add(checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX)

    def _update_workflow_state_with_reached_local_checkpoint(
        self, checkpoint_reached_event, task_name
    ):
        checkpoint_name = checkpoint_reached_event.name()

        self._workflow_state = {
            state_word
            for state_word in self._workflow_state
            if not state_word.endswith(Monitor.CHECKPOINT_REACHED_SUFFIX)
        }
        self._workflow_state.add(
            task_name + "." + checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX
        )

    @classmethod
    def _is_property_satisfied(
        cls, event_time, program_state, component_dictionary, logic_property
    ):
        cls._log_property_analysis(f"Checking property {logic_property[2]}...")
        try:
            declarations = cls._build_declarations(
                program_state, component_dictionary, logic_property
            )
            assumptions = cls._build_assumptions(
                program_state, component_dictionary, logic_property
            )
            not_logic_property_assert = f"(assert (not \n {logic_property[1]} \n))"
            spec = declarations + "\n" + assumptions + "\n" + not_logic_property_assert
            temp_solver = z3.Solver()
            temp_solver.from_string(spec)
            negation_is_sat = z3.sat == temp_solver.check()
            if not negation_is_sat:
                message = f"Property {logic_property[2]} PASSED"
                cls._log_property_analysis(message)
            else:
                cls._log_property_analysis(f"Property {logic_property[2]} FAILED")
                spec_filename = logic_property[2] + "@" + str(event_time) + ".smt2"
                spec_file = open(spec_filename, "w")
                spec_file.write(spec)
                spec_file.close()
                logging.info(f"Specification dumped: [ {spec_filename} ]")
            return negation_is_sat
        except NoValueAssignedToVariable as e:
            logging.error(f"Variable [ {e.getVarname()} ] has no value.")
            raise FormulaError(logic_property[1])
        except UnboundVariables as e:
            logging.error(
                f"Unbounded variables [ {e.getVars()} ] in formula [ {logic_property[2]} ]"
            )
            raise FormulaError(logic_property[1])

    @classmethod
    def _log_property_analysis(cls, message):
        logging.log(LoggingLevel.PROPERTY_ANALYSIS, message)

    @classmethod
    def _are_all_properties_satisfied(
        cls, event_time, program_state, component_dictionary, logic_properties
    ):
        neg_properties_sat = False
        for logic_property in logic_properties:
            if neg_properties_sat:
                break
            try:
                neg_properties_sat = cls._is_property_satisfied(
                    event_time, program_state, component_dictionary, logic_property
                )
            except FormulaError as e:
                logging.error(f"Error in formula [ {e.getFormula} ]")
                raise AnalysisFailed()

        return not neg_properties_sat

    @classmethod
    def _c_type_2_z3_type(cls, varname, var_c_type):
        match var_c_type[0]:
            case "char_t":
                return f"(declare-const {varname} Int)"
            case "uint8_t":
                return f"(declare-const {varname} Int)"
            case "int8_t":
                return f"(declare-const {varname} Int)"
            case "uint16_t":
                return f"(declare-const {varname} Int)"
            case "int16_t":
                return f"(declare-const {varname} Int)"
            case "int":
                return f"(declare-const {varname} Int)"
            case "unsigned int":
                return f"(declare-const {varname} Int)"
            case "float":
                return f"(declare-const {varname} Real)"
            case "double":
                return f"(declare-const {varname} Real)"
            case "char*":
                return f"(declare-const {varname} String)"
            case "uint8_t[]":
                return f"(declare-const {varname} (Array Int Int))"
            case "uint8_t[][]":
                return f"(declare-const {varname} (Array Int (Array Int Int)))"
            case "uint8_t[][][]":
                return (
                    f"(declare-const {varname} (Array Int (Array Int (Array Int Int))))"
                )
            case _:
                raise TypeError()

    @classmethod
    def _build_declaration(cls, varname, vartype):
        declaration = f"{cls._c_type_2_z3_type(varname, vartype)}\n"
        return declaration

    @classmethod
    def _build_assumption(cls, varname, vartype, varvalue):
        assumption = ""
        match len(vartype):
            case 1:
                assumption = assumption + f"(assert (= {varname} {varvalue}))\n"
            case 2:
                assumption = "(assert (and\n"
                for i in range(0, int(vartype[1])):
                    assumption = (
                        assumption + f"(= (select {varname} {i}) {varvalue[i]})\n"
                    )
                assumption = assumption + ") )\n"
            case 3:
                assumption = "(assert (and\n"
                for i in range(0, int(vartype[1])):
                    for j in range(0, int(vartype[2])):
                        assumption = (
                            assumption
                            + f"(= (select (select {varname} {i}) {j}) {varvalue[i][j]})\n"
                        )
                assumption = assumption + ") )\n"
            case 4:
                assumption = "(assert (and\n"
                for i in range(0, int(vartype[1])):
                    for j in range(0, int(vartype[2])):
                        for k in range(0, int(vartype[3])):
                            assumption = (
                                assumption
                                + f"(= (select (select (select {varname} {i}) {j}) {k}) {varvalue[i][j][k]})\n"
                            )
                assumption = assumption + ") )\n"
            case _:
                raise TypeError()

        return assumption

    @classmethod
    def _build_declarations(cls, program_state, component_dictionary, logic_property):
        declarations = ""
        # Building a set from the frozen set containing the variables occurring in the formula
        variables = set()
        for var in logic_property[0]:
            variables.add(var)
        for varname in program_state:
            if varname in variables:
                if isinstance(program_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                declarations = declarations + cls._build_declaration(
                    varname, program_state[varname][0]
                )
                variables.remove(varname)
        for device in component_dictionary:
            dictionary = component_dictionary[device].state()
            for varname in dictionary:
                if varname in variables:
                    # The value of the variable of the state might be iterable.
                    if isinstance(dictionary[varname][1], Iterable):
                        if any(
                            [isinstance(x, NoValue) for x in dictionary[varname][1]]
                        ):
                            raise NoValueAssignedToVariable(varname)
                    elif isinstance(dictionary[varname][1], NoValue):
                        raise NoValueAssignedToVariable(varname)
                    declarations = declarations + cls._build_declaration(
                        varname, dictionary[varname][0]
                    )
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return declarations

    @classmethod
    def _build_assumptions(cls, program_state, component_dictionary, logic_property):
        assumptions = ""
        # Building a set from the frozen set containing the variables occurring in the formula
        variables = set()
        for var in logic_property[0]:
            variables.add(var)
        for varname in program_state:
            if varname in variables:
                if isinstance(program_state[varname][1], NoValue):
                    raise NoValueAssignedToVariable(varname)
                assumptions = assumptions + cls._build_assumption(
                    varname, program_state[varname][0], program_state[varname][1]
                )
                variables.remove(varname)
        for device in component_dictionary:
            dictionary = component_dictionary[device].state()
            for varname in dictionary:
                if varname in variables:
                    # The value of the variable of the state might be iterable.
                    if isinstance(dictionary[varname][1], Iterable):
                        if any(
                            [isinstance(x, NoValue) for x in dictionary[varname][1]]
                        ):
                            raise NoValueAssignedToVariable(varname)
                    elif isinstance(dictionary[varname][1], NoValue):
                        raise NoValueAssignedToVariable(varname)
                    assumptions = assumptions + cls._build_assumption(
                        varname, dictionary[varname][0], dictionary[varname][1]
                    )
                    variables.remove(varname)
        if len(variables) != 0:
            raise UnboundVariables(str(variables))
        return assumptions

    def _process_global_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()

        can_be_reached = self._global_checkpoint_can_be_reached(checkpoint_name)

        checkpoint = self._workflow_specification.global_checkpoint_named(
            checkpoint_name
        )
        try:
            properties_are_met = self.__class__._are_all_properties_satisfied(
                checkpoint_reached_event.time(),
                self._execution_state,
                self._component_dictionary,
                checkpoint.properties(),
            )

            self._update_workflow_state_with_reached_global_checkpoint(
                checkpoint_reached_event
            )

            return can_be_reached and properties_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(checkpoint_reached_event)

    def _process_local_checkpoint_reached(self, checkpoint_reached_event):
        checkpoint_name = checkpoint_reached_event.name()

        can_be_reached = self._local_checkpoint_can_be_reached(checkpoint_name)

        checkpoint = self._workflow_specification.local_checkpoint_named(
            checkpoint_name
        )
        try:
            properties_are_met = self.__class__._are_all_properties_satisfied(
                checkpoint_reached_event.time(),
                self._execution_state,
                self._component_dictionary,
                checkpoint.properties(),
            )

            started_task_name = self._started_task_name_from_state()
            self._update_workflow_state_with_reached_local_checkpoint(
                checkpoint_reached_event, started_task_name
            )

            return can_be_reached and properties_are_met
        except AnalysisFailed:
            logging.critical(f"Analysis FAILED.")
            raise EventError(checkpoint_reached_event)

    def _task_can_start(self, task_name):
        return self._is_workflow_state_valid_for_reaching_element_named(task_name)

    def _global_checkpoint_can_be_reached(self, checkpoint_name):
        return self._is_workflow_state_valid_for_reaching_element_named(checkpoint_name)

    def _local_checkpoint_can_be_reached(self, checkpoint_name):
        there_is_a_task_in_progress = self._there_is_a_task_in_progress()
        if not there_is_a_task_in_progress:
            return False

        task_in_progress_name = self._started_task_name_from_state()
        task_in_progress = self._workflow_specification.task_specification_named(
            task_in_progress_name
        )

        task_in_progress_has_that_checkpoint = any(
            checkpoint.is_named(checkpoint_name)
            for checkpoint in task_in_progress.checkpoints()
        )

        return task_in_progress_has_that_checkpoint

    def _is_workflow_state_valid_for_reaching_element_named(self, element_name):
        preceding_elements = (
            self._workflow_specification.immediately_preceding_elements_for(
                element_name
            )
        )

        follows_a_corresponding_finishing_task = any(
            self._task_had_finished(preceding_element.name())
            for preceding_element in preceding_elements
        )
        follows_a_corresponding_reached_checkpoint = any(
            self._checkpoint_had_been_reached(preceding_element.name())
            for preceding_element in preceding_elements
        )
        is_starting_element_and_state_is_empty = (
            self._workflow_specification.is_starting_element(element_name)
            and self._workflow_state == set()
        )

        return (
            follows_a_corresponding_finishing_task
            or follows_a_corresponding_reached_checkpoint
            or is_starting_element_and_state_is_empty
        )

    def _task_had_started(self, task_name):
        return (task_name + Monitor.TASK_STARTED_SUFFIX) in self._workflow_state

    def _task_had_finished(self, task_name):
        return (task_name + Monitor.TASK_FINISHED_SUFFIX) in self._workflow_state

    def _checkpoint_had_been_reached(self, checkpoint_name):
        state_word = checkpoint_name + Monitor.CHECKPOINT_REACHED_SUFFIX
        return state_word in self._workflow_state

    def _there_is_a_task_in_progress(self):
        return any(
            state_word.endswith(Monitor.TASK_STARTED_SUFFIX)
            for state_word in self._workflow_state
        )

    def _started_task_name_from_state(self):
        # This method assumes that there is a task in progress.
        for state_word in self._workflow_state:
            if state_word.endswith(Monitor.TASK_STARTED_SUFFIX):
                return state_word[: state_word.find(Monitor.TASK_STARTED_SUFFIX)]

    def _pause_verification_if_requested(self, pause_event, stop_event):
        # This is busy waiting. There are better solutions.
        if self._event_was_set(pause_event):
            logging.info(f"Verification paused.")

            while pause_event.is_set():
                if stop_event.is_set():
                    return

            logging.info(f"Verification resumed.")

    def _event_was_set(self, ui_event):
        return ui_event is not None and ui_event.is_set()
