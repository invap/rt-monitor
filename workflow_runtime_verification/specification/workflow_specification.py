import os

from igraph import Graph

from workflow_runtime_verification.specification.workflow_node.checkpoint import (
    Checkpoint,
)
from workflow_runtime_verification.specification.workflow_node.operator import Operator
from workflow_runtime_verification.specification.workflow_node.task_specification import (
    TaskSpecification,
)


class WorkflowSpecification:
    @classmethod
    def new_with(cls, ordered_task_specifications, dependencies):
        return cls(ordered_task_specifications, dependencies)

    @classmethod
    def new_from_file(cls, specification_file_path):
        with open(specification_file_path, "r") as specification_file:
            instance = cls.new_from_open_file(specification_file)
            specification_file.close()
        return instance

    @classmethod
    def new_from_open_file(cls, specification_file):
        encoded_specification = specification_file.read().splitlines()
        specification_file_directory = os.path.dirname(specification_file.name)

        start_node_index = cls._start_node_index_from_file(encoded_specification)

        ordered_nodes = cls._ordered_nodes_from_file(
            encoded_specification, specification_file_directory
        )
        dependencies = cls._dependencies_from_file(encoded_specification)

        return cls(
            ordered_nodes,
            dependencies,
            start_node_index=start_node_index,
            end_node_index=(len(ordered_nodes) - 1),
        )

    def __init__(
        self,
        ordered_elements,
        dependencies,
        start_node_index=None,
        end_node_index=None,
    ):
        super().__init__()
        self._build_workflow_graph(
            ordered_elements, dependencies, start_node_index, end_node_index
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

    @classmethod
    def _ordered_nodes_from_file(
        cls, encoded_specification, specification_file_directory
    ):
        nodes_as_text = encoded_specification[2:]
        nodes_as_text = [
            encoded_task_specification.split(",")
            for encoded_task_specification in nodes_as_text
        ]

        return [
            cls._decode_node(encoded_node, specification_file_directory)
            for encoded_node in nodes_as_text
        ]

    @classmethod
    def _start_node_index_from_file(cls, encoded_specification):
        return int(encoded_specification[1])

    @classmethod
    def _filenames_from_set(cls, filenames_set):
        files_str = (filenames_set.split("{", 1)[1]).rsplit("}", 1)[0]
        filenames = files_str.split(";")
        if filenames[0] == "":
            filenames = []
        return filenames

    @classmethod
    def _decode_node(cls, encoded_node, specification_file_directory):
        if cls._encoded_node_is_task(encoded_node):
            return cls._decode_task_specification(
                encoded_node, specification_file_directory
            )
        elif cls._encoded_node_is_checkpoint(encoded_node):
            return cls._decode_global_checkpoint(
                encoded_node, specification_file_directory
            )
        elif cls._encoded_node_is_operator(encoded_node):
            return cls._decode_operator(encoded_node)

    @classmethod
    def _decode_task_specification(
        cls, encoded_task_specification, specification_file_directory
    ):
        task_name = encoded_task_specification[1]
        preconditions = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_task_specification[2]),
            specification_file_directory,
        )
        postconditions = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_task_specification[3]),
            specification_file_directory,
        )
        local_checkpoints = cls._decode_local_checkpoints(
            ",".join(encoded_task_specification[4:]), specification_file_directory
        )
        return TaskSpecification(
            task_name,
            preconditions=preconditions,
            postconditions=postconditions,
            checkpoints=local_checkpoints,
        )

    @classmethod
    def _decode_global_checkpoint(
        cls, encoded_checkpoint, specification_file_directory
    ):
        checkpoint_name = encoded_checkpoint[1]
        properties = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_checkpoint[2]),
            specification_file_directory,
        )
        return Checkpoint(checkpoint_name, properties)

    @classmethod
    def _decode_local_checkpoints(
        cls, encoded_checkpoints, specification_file_directory
    ):
        encoded_checkpoints = (encoded_checkpoints.split("{", 1)[1]).rsplit("}", 1)[0]
        encoded_checkpoints = encoded_checkpoints.split(",")
        encoded_checkpoints = [
            name + "," + properties
            for name, properties in zip(
                encoded_checkpoints[::2], encoded_checkpoints[1::2]
            )
        ]

        return {
            cls._decode_local_checkpoint(
                encoded_checkpoint, specification_file_directory
            )
            for encoded_checkpoint in encoded_checkpoints
        }

    @classmethod
    def _decode_local_checkpoint(cls, encoded_checkpoint, specification_file_directory):
        encoded_checkpoint = (encoded_checkpoint.split("<", 1)[1]).rsplit(">", 1)[0]
        checkpoint_name = encoded_checkpoint.split(",")[0]
        properties = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_checkpoint.split(",")[1]),
            specification_file_directory,
        )
        return Checkpoint(checkpoint_name, properties)

    @classmethod
    def _decode_operator(cls, encoded_node):
        return Operator.new_of_type(encoded_node[1])

    @classmethod
    def _smt2_property_from_file(cls, file_name, specification_file_directory):
        file_name_ext = file_name + ".protosmt2"
        file_path = os.path.join(specification_file_directory, file_name_ext)
        with open(file_path, "r") as file:
            vars = (file.readline().split("\n")[0]).split(",")
            spec_vars = set()
            if vars[0] != "None":
                for var in vars:
                    spec_vars.add(var)
            spec = ""
            for line in file:
                spec = spec + line
            file.close()
            s = (frozenset(spec_vars), spec, file_name)
        return s

    @classmethod
    def _smt2_properties_from_files(cls, file_names, specification_file_directory):
        properties = set()
        for file_name in file_names:
            properties.add(
                cls._smt2_property_from_file(file_name, specification_file_directory)
            )
        return properties

    @classmethod
    def _dependencies_from_file(cls, encoded_specification):
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
        nodes = self._graph.vs[self._workflow_node_attribute_name()]
        return [node for node in nodes if isinstance(node, TaskSpecification)]

    def _global_checkpoints(self):
        nodes = self._graph.vs[self._workflow_node_attribute_name()]
        return [node for node in nodes if isinstance(node, Checkpoint)]

    def _build_workflow_graph(
        self, ordered_elements, dependencies, start_node_index, end_node_index
    ):
        amount_of_elements = len(ordered_elements)
        list_of_edges = list(dependencies)

        self._graph = Graph(
            amount_of_elements,
            list_of_edges,
            vertex_attrs={self._workflow_node_attribute_name(): ordered_elements},
            directed=True,
        )

        self._wrap_graph_in_cycle(start_node_index, end_node_index)

    def _wrap_graph_in_cycle(self, start_node_index, end_node_index):
        if start_node_index is None:
            graph_start_node = [
                node for node in self._graph.vs if node.indegree() == 0
            ][0]
        else:
            graph_start_node = self._graph.vs[start_node_index]

        if end_node_index is None:
            graph_end_node = [node for node in self._graph.vs if node.outdegree() == 0][
                0
            ]
        else:
            graph_end_node = self._graph.vs[end_node_index]

        self._graph.add_edge(graph_end_node, graph_start_node)
        self._starting_element = graph_start_node[self._workflow_node_attribute_name()]

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

    @classmethod
    def _encoded_node_is_task(cls, encoded_node):
        return cls._encoded_node_type(encoded_node) == "task"

    @classmethod
    def _encoded_node_is_checkpoint(cls, encoded_node):
        return cls._encoded_node_type(encoded_node) == "checkpoint"

    @classmethod
    def _encoded_node_is_operator(cls, encoded_node):
        return cls._encoded_node_type(encoded_node) == "operator"

    @classmethod
    def _encoded_node_type(cls, encoded_node):
        return encoded_node[0].split(":")[1]
