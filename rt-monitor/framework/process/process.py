# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from framework.process.process_node.checkpoint import Checkpoint
from framework.process.process_node.task import Task


class Process:
    def __init__(self, graph, starting_element, variables):
        super().__init__()
        self._graph = graph
        self._starting_element = starting_element
        self._variables = variables

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
        current_graph_node = self._graph_node_for_process_node(element)

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

    def variables(self):
        return self._variables

    def _element_named(self, element_name):
        if self.task_exists(element_name):
            return self.task_specification_named(element_name)
        elif self.global_checkpoint_exists(element_name):
            return self.global_checkpoint_named(element_name)

    def _graph_node_for_process_node(self, task_specification):
        return self._graph.vs.find(process_node=task_specification)

    def _task_specifications(self):
        nodes = self._graph.vs[Process._process_node_attribute_name()]
        return [node for node in nodes if isinstance(node, Task)]

    def _global_checkpoints(self):
        nodes = self._graph.vs[Process._process_node_attribute_name()]
        return [node for node in nodes if isinstance(node, Checkpoint)]

    def _immediately_preceding_elements_for_graph_node(self, current_graph_node):
        immediate_graph_node_predecessors = current_graph_node.predecessors()

        preceding_elements = set()
        for predecessor in immediate_graph_node_predecessors:
            process_node = predecessor[self._process_node_attribute_name()]

            is_task = isinstance(process_node, Task)
            is_checkpoint = isinstance(process_node, Checkpoint)
            if is_task or is_checkpoint:
                preceding_elements.add(process_node)
            else:
                preceding_elements.update(
                    self._immediately_preceding_elements_for_graph_node(predecessor)
                )

        return preceding_elements

    @staticmethod
    def _process_node_attribute_name():
        return "process_node"
