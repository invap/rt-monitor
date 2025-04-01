# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging

from igraph import Graph

from rt_monitor.errors.process_errors import (
    ProcessSpecificationError,
    TaskSpecificationError,
    GlobalCheckpointSpecificationError,
    VariablesSpecificationError
)
from rt_monitor.framework.process.process import Process
from rt_monitor.framework.process.process_node.checkpoint import Checkpoint
from rt_monitor.framework.process.process_node.task import Task


class GraphProcess(Process):
    def __init__(self, dfa, tasks, checkpoints, variables):
        super().__init__(variables)
        self._dfa = dfa
        self._tasks = tasks
        self._checkpoints = checkpoints

    @staticmethod
    def process_from_toml_dict(process_dict, files_path):
        reverse_node_name_map = {}  # Build a reverse map between node numbers and node names
        ordered_nodes = []
        for node_number in range(0, len(process_dict["structure"]["nodes"])):
            node = process_dict["structure"]["nodes"][node_number]
            if not isinstance(node, list) or len(node) != 2:
                logging.error(f"The {node_number + 1} node in the list of nodes is not well formed. It should "
                              f"be [ node name , node type ]")
                raise ProcessSpecificationError()
            node_name = process_dict["structure"]["nodes"][node_number][0]
            node_type = process_dict["structure"]["nodes"][node_number][1]
            reverse_node_name_map[node_name] = node_number
            # In the case of operators the shape of node_type is 'operator:<operator type>'.
            split_node_type = node_type.split(":", 1)
            match split_node_type[0]:
                case "task":
                    try:
                        decoded_task = Process._decode_task(node_name, process_dict["tasks"], files_path)
                    except TaskSpecificationError:
                        logging.error(f"Error decoding task from process node [ {node_name} ].")
                        raise ProcessSpecificationError()
                    ordered_nodes.append(decoded_task)
                case "checkpoint":
                    try:
                        global_checkpoint = Process._decode_global_checkpoint(
                            node_name,
                            process_dict["checkpoints"],
                            files_path
                        )
                    except GlobalCheckpointSpecificationError:
                        logging.error(f"Error decoding global checkpoint from process node [ {node_name} ].")
                        raise ProcessSpecificationError()
                    ordered_nodes.append(global_checkpoint)
                case _:
                    logging.error(f"Type [ {node_type} ] of process node [ {node_name} ] unknown. Please "
                                  f"tell me that you did not forget to put the 'operator:' in front of a "
                                  f"node of type operator...")
                    raise ProcessSpecificationError()
        dependencies = {(reverse_node_name_map[src], reverse_node_name_map[trg]) for [src, trg] in
                        process_dict["structure"]["edges"]}
        amount_of_elements = len(ordered_nodes)
        graph = Graph(
            amount_of_elements,
            dependencies,
            vertex_attrs={"process_node": ordered_nodes},
            directed=True,
        )
        starting_element = graph.vs[reverse_node_name_map[process_dict["structure"]["start"]]]["process_node"]
        try:
            variables = _get_variables_from_nodes([ordered_nodes[node] for node in range(0, amount_of_elements)])
        except VariablesSpecificationError:
            logging.error(f"Variables specification error.")
            raise ProcessSpecificationError()
        else:
            return GraphProcess(graph, starting_element, variables)

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

    def variables(self):
        return self._variables


# Raises: UnsupportedNodeType(), PropertySpecificationError()
def _get_variables_from_nodes(nodes):
    variables = {}
    for node in nodes:
        if isinstance(node, Task):
            for formula in node.preconditions():
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
            for formula in node.postconditions():
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
            for checkpoint in node.checkpoints():
                for formula in checkpoint.properties():
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
        elif isinstance(node, Checkpoint):
            for formula in node.properties():
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
        else:
            # Nodes have already been checked for being of type Task or Checkpoint.
            pass
    return variables
