# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import os

from igraph import Graph

from workflow_runtime_verification.specification.Py_property import PyProperty
from workflow_runtime_verification.specification.SMT2_property import SMT2Property
from workflow_runtime_verification.specification.SymPy_property import SymPyProperty
from workflow_runtime_verification.specification.specification_errors import (
    UnsupportedNodeType,
    PropertyTypeError,
    InconsistentVariableDeclaration
)
from workflow_runtime_verification.specification.workflow_node.checkpoint import Checkpoint
from workflow_runtime_verification.specification.workflow_node.operator import Operator
from workflow_runtime_verification.specification.workflow_node.task_specification import TaskSpecification


class WorkflowSpecification:
    @staticmethod
    def new_from_file(specification_file_path):
        with open(specification_file_path, "r") as specification_file:
            instance = WorkflowSpecification.new_from_open_file(specification_file)
            specification_file.close()
        return instance

    @classmethod
    def new_from_open_file(cls, specification_file):
        encoded_specification = specification_file.read().splitlines()
        specification_file_directory = os.path.dirname(specification_file.name)

        start_node_index = WorkflowSpecification._start_node_index_from_file(encoded_specification)

        ordered_nodes = WorkflowSpecification._ordered_nodes_from_file(
            encoded_specification, specification_file_directory
        )
        dependencies = WorkflowSpecification._dependencies_from_file(encoded_specification)

        return WorkflowSpecification(
            ordered_nodes,
            dependencies,
            start_node_index=start_node_index
        )

    def __init__(self, ordered_elements, dependencies, start_node_index):
        super().__init__()
        self._build_workflow_graph(
            ordered_elements, dependencies, start_node_index
        )

    def task_exists(self, task_name):
        return any(task.is_named(task_name) for task in self._task_specifications())

    def global_checkpoint_exists(self, checkpoint_name):
        return any(
            checkpoint.is_named(checkpoint_name)
            for checkpoint in self._global_checkpoints()
        )

    def local_checkpoint_exists(self, checkpoint_name):
        return any(
            task.has_checkpoint_named(checkpoint_name)
            for task in self._task_specifications()
        )

    def is_starting_element(self, element_name):
        element = self._element_named(element_name)
        return element == self._starting_element

    def immediately_preceding_elements_for(self, element_name):
        element = self._element_named(element_name)
        current_graph_node = self._graph_node_for_workflow_node(element)

        return self._immediately_preceding_elements_for_graph_node(current_graph_node)

    def task_specification_named(self, task_name):
        # This method assumes there is a task named that way.
        for task_specification in self._task_specifications():
            if task_specification.is_named(task_name):
                return task_specification

    def global_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a global checkpoint named that way.
        for checkpoint in self._global_checkpoints():
            if checkpoint.is_named(checkpoint_name):
                return checkpoint

    def local_checkpoint_named(self, checkpoint_name):
        # This method assumes there is a local checkpoint named that way.
        for task in self._task_specifications():
            if task.has_checkpoint_named(checkpoint_name):
                return task.checkpoint_named(checkpoint_name)

    def get_variables(self):
        return self._variables

    @staticmethod
    def _ordered_nodes_from_file(encoded_specification, specification_file_directory):
        nodes_as_text = encoded_specification[2:]
        nodes_as_text = [
            encoded_task_specification.split(",")
            for encoded_task_specification in nodes_as_text
        ]
        return [
            WorkflowSpecification._decode_node(encoded_node, specification_file_directory)
            for encoded_node in nodes_as_text
        ]

    @staticmethod
    def _start_node_index_from_file(encoded_specification):
        return int(encoded_specification[1])

    @staticmethod
    def _filenames_from_set(filenames_set):
        files_str = (filenames_set.split("{", 1)[1]).rsplit("}", 1)[0]
        filenames = files_str.split(";")
        if filenames[0] == "":
            filenames = []
        return filenames

    @staticmethod
    def _decode_node(encoded_node, specification_file_directory):
        if WorkflowSpecification._encoded_node_is_task(encoded_node):
            return WorkflowSpecification._decode_task_specification(
                encoded_node, specification_file_directory
            )
        elif WorkflowSpecification._encoded_node_is_checkpoint(encoded_node):
            return WorkflowSpecification._decode_global_checkpoint(
                encoded_node, specification_file_directory
            )
        elif WorkflowSpecification._encoded_node_is_operator(encoded_node):
            return WorkflowSpecification._decode_operator(encoded_node)

    @staticmethod
    def _decode_task_specification(encoded_task_specification, specification_file_directory):
        task_name = encoded_task_specification[1]
        preconditions = WorkflowSpecification._properties_from_files(
            WorkflowSpecification._filenames_from_set(encoded_task_specification[2]),
            specification_file_directory,
        )
        postconditions = WorkflowSpecification._properties_from_files(
            WorkflowSpecification._filenames_from_set(encoded_task_specification[3]),
            specification_file_directory,
        )
        local_checkpoints = WorkflowSpecification._decode_local_checkpoints(
            ",".join(encoded_task_specification[4:]), specification_file_directory
        )
        return TaskSpecification(
            task_name,
            preconditions=preconditions,
            postconditions=postconditions,
            checkpoints=local_checkpoints,
        )

    @staticmethod
    def _decode_global_checkpoint(encoded_checkpoint, specification_file_directory):
        checkpoint_name = encoded_checkpoint[1]
        properties = WorkflowSpecification._properties_from_files(
            WorkflowSpecification._filenames_from_set(encoded_checkpoint[2]),
            specification_file_directory,
        )
        return Checkpoint(checkpoint_name, properties)

    @staticmethod
    def _decode_local_checkpoints(encoded_checkpoints, specification_file_directory):
        encoded_checkpoints = (encoded_checkpoints.split("{", 1)[1]).rsplit("}", 1)[0]
        encoded_checkpoints = encoded_checkpoints.split(",")
        encoded_checkpoints = [
            name + "," + properties
            for name, properties in zip(
                encoded_checkpoints[::2], encoded_checkpoints[1::2]
            )
        ]

        return {
            WorkflowSpecification._decode_local_checkpoint(
                encoded_checkpoint, specification_file_directory
            )
            for encoded_checkpoint in encoded_checkpoints
        }

    @staticmethod
    def _decode_local_checkpoint(encoded_checkpoint, specification_file_directory):
        encoded_checkpoint = (encoded_checkpoint.split("<", 1)[1]).rsplit(">", 1)[0]
        checkpoint_name = encoded_checkpoint.split(",")[0]
        properties = WorkflowSpecification._properties_from_files(
            WorkflowSpecification._filenames_from_set(encoded_checkpoint.split(",")[1]),
            specification_file_directory,
        )
        return Checkpoint(checkpoint_name, properties)

    @staticmethod
    def _decode_operator(encoded_node):
        return Operator.new_of_type(encoded_node[1])

    @staticmethod
    def _properties_from_files(file_names, specification_file_directory):
        properties = set()
        for file_name in file_names:
            properties.add(WorkflowSpecification._property_from_file(file_name, specification_file_directory))
        return properties

    @staticmethod
    def _property_from_file(file_name, specification_file_directory):
        decoded_filename = file_name.split(":")
        property_type = decoded_filename[0]
        filename = decoded_filename[1]
        match property_type:
            case "smt2":
                return SMT2Property.property_from_file(filename, specification_file_directory)
            case "sympy":
                return SymPyProperty.property_from_file(filename, specification_file_directory)
            case "py":
                return PyProperty.property_from_file(filename, specification_file_directory)
            case _:
                raise PropertyTypeError(property_type, filename)

    @staticmethod
    def _dependencies_from_file(encoded_specification):
        encoded_dependencies = encoded_specification[0].replace(" ", "")
        dependencies_as_text = encoded_dependencies.split("{", 1)[1].rsplit("}", 1)[0]
        node_indices = dependencies_as_text.replace("(", "").replace(")", "").split(",")

        if node_indices[0] == "":
            return set()

        return {
            (int(node_indices[index]), int(node_indices[index + 1]))
            for index in range(0, len(node_indices), 2)
        }

    def _element_named(self, element_name):
        if self.task_exists(element_name):
            return self.task_specification_named(element_name)
        elif self.global_checkpoint_exists(element_name):
            return self.global_checkpoint_named(element_name)

    def _graph_node_for_workflow_node(self, task_specification):
        return self._graph.vs.find(workflow_node=task_specification)

    def _task_specifications(self):
        nodes = self._graph.vs[WorkflowSpecification._workflow_node_attribute_name()]
        return [node for node in nodes if isinstance(node, TaskSpecification)]

    def _global_checkpoints(self):
        nodes = self._graph.vs[WorkflowSpecification._workflow_node_attribute_name()]
        return [node for node in nodes if isinstance(node, Checkpoint)]

    def _build_workflow_graph(self, ordered_elements, dependencies, start_node_index):
        amount_of_elements = len(ordered_elements)
        list_of_edges = list(dependencies)

        self._graph = Graph(
            amount_of_elements,
            list_of_edges,
            vertex_attrs={self._workflow_node_attribute_name(): ordered_elements},
            directed=True,
        )
        self._starting_element = self._graph.vs[start_node_index][self._workflow_node_attribute_name()]
        self._variables = get_variables_from_nodes([ordered_elements[node] for node in range(0, amount_of_elements) if
                                                    not isinstance(ordered_elements[node], Operator)])

    def _immediately_preceding_elements_for_graph_node(self, current_graph_node):
        immediate_graph_node_predecessors = current_graph_node.predecessors()

        preceding_elements = set()
        for predecessor in immediate_graph_node_predecessors:
            workflow_node = predecessor[self._workflow_node_attribute_name()]

            is_task = isinstance(workflow_node, TaskSpecification)
            is_checkpoint = isinstance(workflow_node, Checkpoint)
            if is_task or is_checkpoint:
                preceding_elements.add(workflow_node)
            else:
                preceding_elements.update(
                    self._immediately_preceding_elements_for_graph_node(predecessor)
                )

        return preceding_elements

    @staticmethod
    def _workflow_node_attribute_name():
        return "workflow_node"

    @staticmethod
    def _encoded_node_is_task(encoded_node):
        return WorkflowSpecification._encoded_node_type(encoded_node) == "task"

    @staticmethod
    def _encoded_node_is_checkpoint(encoded_node):
        return WorkflowSpecification._encoded_node_type(encoded_node) == "checkpoint"

    @staticmethod
    def _encoded_node_is_operator(encoded_node):
        return WorkflowSpecification._encoded_node_type(encoded_node) == "operator"

    @staticmethod
    def _encoded_node_type(encoded_node):
        return encoded_node[0].split(":")[1]


def get_variables_from_nodes(nodes):
    variables = {}
    for node in nodes:
        if isinstance(node, TaskSpecification):
            for formula in node.preconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        raise InconsistentVariableDeclaration(variable, formula.variables()[variable])
                    variables[variable] = formula.variables()[variable]
            for formula in node.postconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        raise InconsistentVariableDeclaration(variable, formula.variables()[variable])
                    variables[variable] = formula.variables()[variable]
            for checkpoint in node.checkpoints():
                for formula in checkpoint.properties():
                    for variable in formula.variables():
                        if variable in variables and not variables[variable] == formula.variables()[variable]:
                            raise InconsistentVariableDeclaration(variable, formula.variables()[variable])
                        variables[variable] = formula.variables()[variable]
        elif isinstance(node, Checkpoint):
            for formula in node.properties():
                variables.update(formula.variables())
        else:
            raise UnsupportedNodeType(node.__class__)
    return variables
