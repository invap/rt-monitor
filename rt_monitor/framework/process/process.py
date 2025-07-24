# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import itertools
from abc import ABC, abstractmethod
import logging
# Create a logger for the process component
logger = logging.getLogger(__name__)

from rt_monitor.errors.process_errors import (
    PropertySpecificationError,
    TaskSpecificationError,
    CheckpointSpecificationError,
    ProcessSpecificationError,
    VariableSpecificationError
)
from rt_monitor.framework.process.process_node.checkpoint import Checkpoint
from rt_monitor.framework.process.process_node.task import Task
from rt_monitor.framework.process.process_node.property import Property


class Process(ABC):
    def __init__(self, dfa, tasks, checkpoints, properties, variables):
        self._dfa = dfa
        self._tasks = tasks
        self._checkpoints = checkpoints
        self._properties = properties
        self._variables = variables

    def dfa(self):
        return self._dfa

    def variables(self):
        return self._variables

    @staticmethod
    @abstractmethod
    def process_from_toml_dict(process_dict, files_path):
        raise NotImplementedError

    @staticmethod
    # Raises: ProcessSpecificationError()
    def dictionaries_from_toml_dict(process_dict, files_path):
        # Build dictionaries containing tasks, checkpoints and properties
        try:
            properties = Process._decode_properties(process_dict["properties"],
                                                    files_path) if "properties" in process_dict else {}
        except PropertySpecificationError:
            logger.error(f"Property specification error.")
            raise ProcessSpecificationError()
        try:
            checkpoints = Process._decode_checkpoints(
                process_dict["checkpoints"]) if "checkpoints" in process_dict else {}
        except CheckpointSpecificationError:
            logger.error(f"Checkpoint specification error.")
            raise ProcessSpecificationError()
        try:
            tasks = Process._decode_tasks(process_dict["tasks"]) if "tasks" in process_dict else {}
        except TaskSpecificationError:
            logger.error(f"Task specification error.")
            raise ProcessSpecificationError()
        # Check integrity of the process:
        # The properties appearing in the checkpoints must be declared as properties
        if any({property_name not in properties.keys() for property_name in
                list(itertools.chain.from_iterable(checkpoints[checkpoint].properties() for
                                                   checkpoint in checkpoints))}):
            logger.error(f"Undeclared property in checkpoint.")
            raise ProcessSpecificationError()
        # The properties appearing in the peconditions and postconditions of tasks must be declared as properties
        if (any({property_name not in properties.keys() for property_name in
                list(itertools.chain.from_iterable(tasks[task].preconditions() for
                                                   task in tasks))}) or
            any({property_name not in properties.keys() for property_name in
                 list(itertools.chain.from_iterable(tasks[task].postconditions() for
                                                    task in tasks))})):
            logger.error(f"Undeclared property in task.")
            raise ProcessSpecificationError()
        # The checkpoints appearing in the tasks must be declared as checkpoints
        if any({checkpoint_name not in checkpoints.keys() for checkpoint_name in
                list(itertools.chain.from_iterable(tasks[task].checkpoints() for
                                                   task in tasks))}):
            logger.error(f"Undeclared checkpoint in task.")
            raise ProcessSpecificationError()
        return tasks, checkpoints, properties

    @staticmethod
    # Raises: PropertySpecificationError()
    def _decode_properties(properties_list, files_path):
        properties = {}
        for prop_dict in properties_list:
            if "name" not in prop_dict:
                logger.error(f"Property must have a name.")
                raise PropertySpecificationError()
            try:
                decoded_property = Property.property_from_toml_dict(prop_dict["name"], prop_dict, files_path)
            except PropertySpecificationError:
                logger.error(f"Error decoding property from process [ {prop_dict["name"]} ].")
                raise ProcessSpecificationError()
            properties[prop_dict["name"]] = decoded_property
        return properties

    @staticmethod
    # Raises: CheckpointSpecificationError()
    def _decode_checkpoints(checkpoints_list):
        checkpoints = {}
        for checkpoint_dict in checkpoints_list:
            if "name" not in checkpoint_dict:
                logger.error(f"Checkpoint must have a name.")
                raise CheckpointSpecificationError()
            try:
                decoded_checkpoint = Checkpoint.checkpoint_from_toml_dict(checkpoint_dict["name"], checkpoint_dict)
            except PropertySpecificationError:
                logger.error(f"Error decoding property from process [ {checkpoint_dict["name"]} ].")
                raise ProcessSpecificationError()
            checkpoints[checkpoint_dict["name"]] = decoded_checkpoint
        return checkpoints

    @staticmethod
    def _decode_tasks(tasks_list):
        tasks = {}
        for task_dict in tasks_list:
            if "name" not in task_dict:
                logger.error(f"Property must have a name.")
                raise TaskSpecificationError()
            try:
                decoded_task = Task.task_from_toml_dict(task_dict["name"], task_dict)
            except PropertySpecificationError:
                logger.error(f"Error decoding task from process [ {task_dict["name"]} ].")
                raise ProcessSpecificationError()
            tasks[task_dict["name"]] = decoded_task
        return tasks

    # Raises: VariablesSpecificationError()
    @staticmethod
    def _get_variables_from_properties(properties):
        variables = {}
        for property_name in properties:
            variables_in_prop = properties[property_name].variables()
            for variable_name in variables_in_prop:
                if variable_name in variables:
                    # If there are multiple declarations for a variable, their class (i.e., ?[0]) and type (i.e., ?[1])
                    # must be consistent
                    if (variables_in_prop[variable_name][0] != variables[variable_name][0] or
                            variables_in_prop[variable_name][1] != variables[variable_name][1]):
                        logger.error(f"Inconsistent declaration for variable [ {variable_name} ] - "
                                      f"[ {variables_in_prop[variable_name]} != {variables[variable_name]} ].")
                        raise VariableSpecificationError()
                else:
                    variables[variable_name] = variables_in_prop[variable_name]
        return variables

    def properties(self):
        return self._properties

    def tasks(self):
        return self._tasks

    def checkpoints(self):
        return self._checkpoints
