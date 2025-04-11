# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from abc import ABC, abstractmethod

import graphviz
from pyformlang.finite_automaton import Symbol

from rt_monitor.errors.process_errors import (
    PropertySpecificationError,
    TaskSpecificationError,
    LocalCheckpointSpecificationError,
    GlobalCheckpointSpecificationError, ProcessSpecificationError, VariablesSpecificationError
)

from rt_monitor.framework.process.process_node.checkpoint import Checkpoint
from rt_monitor.framework.process.process_node.task import Task
from rt_monitor.framework.process.property import Property


class Process(ABC):
    def __init__(self, dfa, tasks, checkpoints, variables):
        self._variables = variables
        self._dfa = dfa
        self._tasks = tasks
        self._checkpoints = checkpoints

    def dfa(self):
        return self._dfa

    def variables(self):
        return self._variables

    @staticmethod
    @abstractmethod
    def process_from_toml_dict(process_dict, files_path):
        raise NotImplementedError

    @staticmethod
    def dictionaries_from_toml_dict(process_dict, files_path):
        # Build dictionaries containing tasks and checkpoints
        tasks = {}
        for task in process_dict["tasks"]:
            try:
                decoded_task = Process._decode_task(task["name"], process_dict["tasks"], files_path)
            except TaskSpecificationError:
                logging.error(f"Error decoding task from process [ {task["name"]} ].")
                raise ProcessSpecificationError()
            tasks[task["name"]] = decoded_task
        checkpoints = {}
        for checkpoint in process_dict["checkpoints"]:
            try:
                decoded_checkpoint = Process._decode_global_checkpoint(checkpoint["name"], process_dict["checkpoints"], files_path)
            except GlobalCheckpointSpecificationError:
                logging.error(f"Error decoding task from process [ {checkpoint["name"]} ].")
                raise ProcessSpecificationError()
            checkpoints[checkpoint["name"]] = decoded_checkpoint
        return tasks, checkpoints

    def task_exists(self, task_name):
        return task_name in self._tasks

    def global_checkpoint_exists(self, checkpoint_name):
        return checkpoint_name in self._checkpoints

    def local_checkpoint_exists(self, checkpoint_name):
        return any(any(checkpoint == checkpoint_name for checkpoint in task.checkpoints()) for task in self._tasks.values())

    def task_specification_named(self, task_name):
        # This method assumes there is a task named that way.
        return self._tasks[task_name]

    def global_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a global checkpoint named that way.
        return self._checkpoints[checkpoint_name]

    def local_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a local checkpoint named that way.
        for task in self._tasks.values():
            if checkpoint_name in task.checkpoints():
                return task.checkpoints()[checkpoint_name]

    # Raises: TaskSpecificationError()
    @staticmethod
    def _decode_task(task_name, toml_tasks_list, files_path):
        preconditions_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name:
                found = True
                preconditions_list = toml_tasks_list[i]["pres"] if "pres" in toml_tasks_list[i] else []
        try:
            preconditions = Process._properties_from_list(preconditions_list, files_path)
        except PropertySpecificationError:
            logging.error(f"Error decoding preconditions for task [ {task_name} ].")
            raise TaskSpecificationError()
        postconditions_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name and "posts" in toml_tasks_list[i]:
                found = True
                postconditions_list = toml_tasks_list[i]["posts"] if "posts" in toml_tasks_list[i] else []
        try:
            postconditions = Process._properties_from_list(postconditions_list, files_path)
        except PropertySpecificationError:
            logging.error(f"Error decoding postconditions for task [ {task_name} ].")
            raise TaskSpecificationError()
        checkpoints_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name:
                found = True
                checkpoints_list = toml_tasks_list[i]["checkpoints"] if "checkpoints" in toml_tasks_list[i] else []
        try:
            local_checkpoints = Process._decode_local_checkpoints(checkpoints_list, files_path)
        except LocalCheckpointSpecificationError:
            logging.error(f"Error decoding local checkpoints for task [ {task_name} ].")
            raise TaskSpecificationError()
        return Task(
            task_name,
            preconditions=preconditions,
            postconditions=postconditions,
            checkpoints=local_checkpoints
        )

    # Raises: GlobalCheckpointSpecificationError()
    @staticmethod
    def _decode_global_checkpoint(checkpoint_name, toml_checkpoints_list, files_path):
        properties_list = []
        found = False
        for i in range(0, len(toml_checkpoints_list)):
            if found:
                break
            if toml_checkpoints_list[i]["name"] == checkpoint_name:
                found = True
                properties_list = toml_checkpoints_list[i]["properties"]
        try:
            properties_from_list = Process._properties_from_list(properties_list, files_path)
        except PropertySpecificationError:
            logging.error(f"Error decoding global checkpoint [ {checkpoint_name} ].")
            raise GlobalCheckpointSpecificationError()
        return Checkpoint(checkpoint_name, properties_from_list)

    # Raises: LocalCheckpointSpecificationError()
    @staticmethod
    def _decode_local_checkpoints(checkpoints_list, files_path):
        checkpoints = {}
        if not checkpoints_list == [{}]:
            for checkpoint in checkpoints_list:
                if "name" not in checkpoint:
                    logging.error(f"Local checkpoint name missing.")
                    raise LocalCheckpointSpecificationError()
                if "properties" not in checkpoint:
                    logging.error(f"Properties of local checkpoint [ {checkpoint["name"]} ] missing.")
                    raise LocalCheckpointSpecificationError()
                try:
                    properties_from_list = Process._properties_from_list(checkpoint["properties"], files_path)
                except PropertySpecificationError:
                    logging.error(f"Error decoding local checkpoint [ {checkpoint["name"]} ].")
                    raise LocalCheckpointSpecificationError()
                checkpoints[checkpoint["name"]] = Checkpoint(checkpoint["name"], properties_from_list)
        return checkpoints

    # Propagates: PropertySpecificationError()
    @staticmethod
    def _properties_from_list(properties_list, files_path):
        properties = set()
        if not properties_list == [{}]:
            for prop in properties_list:
                if "name" not in prop:
                    logging.error(f"Property must have a name.")
                    raise PropertySpecificationError()
                if "file" in prop and "formula" in prop:
                    logging.error(f"Property [ {prop["name"]} ] cannot have both a file specification and an inline specification.")
                    raise PropertySpecificationError()
                if "file" not in prop and "formula" not in prop:
                    logging.error(f"Property [ {prop["name"]} ] source unknown not found.")
                    raise PropertySpecificationError()
                if "formula" in prop:
                    # This operation might raise a PropertySpecificationError exception.
                    properties.add(Property.property_from_toml_dict(prop["name"], prop))
                else:  # "file" in prop
                    file_name = prop["file"] \
                        if prop["file"][0] == "/" or prop["file"][0] == "." \
                        else files_path + prop["file"]
                    # This operation might raise a PropertySpecificationError exception.
                    properties.add(Property.property_from_file(prop["name"], file_name))
        return properties

    # Raises: VariablesSpecificationError()
    @staticmethod
    def _get_variables_from_dicts(tasks, checkpoints):
        variables = {}
        for task_name in tasks:
            for formula in tasks[task_name].preconditions():
                for variable in formula.variables():
                    if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                        logging.error(
                            f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                        raise VariablesSpecificationError()
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise VariablesSpecificationError()
                    variables[variable] = formula.variables()[variable]
            for formula in tasks[task_name].postconditions():
                for variable in formula.variables():
                    if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                        logging.error(
                            f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                        raise VariablesSpecificationError()
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise VariablesSpecificationError()
                    variables[variable] = formula.variables()[variable]
            for checkpoint_name in tasks[task_name].checkpoints():
                for formula in tasks[task_name].checkpoints()[checkpoint_name].properties():
                    for variable in formula.variables():
                        if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                            logging.error(
                                f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                            raise VariablesSpecificationError()
                        if variable in variables and not variables[variable] == formula.variables()[variable]:
                            logging.error(
                                f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                            raise VariablesSpecificationError()
                        variables[variable] = formula.variables()[variable]
        for checkpoint_name in checkpoints:
            for formula in checkpoints[checkpoint_name].properties():
                for variable in formula.variables():
                    if formula.variables()[variable][0] not in {"Component", "State", "Clock"}:
                        logging.error(
                            f"Variables class [ {formula.variables()[variable][0]} ] unsupported.")
                        raise VariablesSpecificationError()
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise VariablesSpecificationError()
                    variables[variable] = formula.variables()[variable]
        return variables


def draw_dfa(dfa, dfa_name):
    # Initialize Graphviz
    dot = graphviz.Digraph(engine="dot")

    # Add states
    for state in dfa.states:
        if state in dfa.final_states:
            dot.node(str(state), shape="doublecircle")
        else:
            dot.node(str(state))

    # Add start state arrow
    dot.node("__start__", shape="none", width="0", height="0")
    dot.edge("__start__", str(dfa.start_state))

    # Add transitions
    for state in dfa.states:
        for symbol in dfa.symbols:
            next_state = dfa(state, Symbol(symbol))
            if next_state is not None:
                dot.edge(str(state), str(next_state), label=str(symbol))

    # Render the graph
    dot.render(dfa_name, format="png", view=True)
