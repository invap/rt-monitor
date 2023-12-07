import os
from igraph import Graph

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

        ordered_task_specifications = cls._ordered_task_specifications_from_file(
            encoded_specification, specification_file_directory
        )
        dependencies = cls._dependencies_from_file(encoded_specification)
        checkpoint_properties = cls._checkpoint_properties_from_file(
            encoded_specification, specification_file_directory
        )

        return cls(
            ordered_task_specifications,
            dependencies,
            start_node_index=0,
            end_node_index=(len(ordered_task_specifications) - 1),
            checkpoint_properties=checkpoint_properties,
        )

    def __init__(
        self,
        ordered_task_specifications,
        dependencies,
        start_node_index=None,
        end_node_index=None,
        checkpoint_properties=None,
    ):
        super().__init__()

        if checkpoint_properties is None:
            checkpoint_properties = dict()

        self._checkpoint_properties = checkpoint_properties
        self._build_workflow_graph(
            ordered_task_specifications, dependencies, start_node_index, end_node_index
        )

    def task_exists(self, task_name):
        return any(task.is_named(task_name) for task in self._task_specifications())

    def checkpoint_exists(self, checkpoint_name):
        return checkpoint_name in self._checkpoint_properties

    def is_starting_task(self, task_name):
        task_specification = self.task_specification_named(task_name)
        return task_specification == self._starting_task_specification

    def immediately_preceding_tasks_for(self, task_name):
        task_specification = self.task_specification_named(task_name)
        preceding_task_specifications = set()

        current_graph_node = self._graph_node_for_task_specification(task_specification)
        immediate_graph_node_predecessors = current_graph_node.predecessors()

        for predecessor in immediate_graph_node_predecessors:
            task_specification = predecessor[self._task_specification_attribute_name()]
            preceding_task_specifications.add(task_specification)

        return preceding_task_specifications

    @classmethod
    def _ordered_task_specifications_from_file(
        cls, encoded_specification, specification_file_directory
    ):
        encoded_task_specifications = encoded_specification[2:]
        encoded_task_specifications = [
            encoded_task_specification.split(",")
            for encoded_task_specification in encoded_task_specifications
        ]

        return [
            cls._decode_task_specification(
                encoded_task_specification, specification_file_directory
            )
            for encoded_task_specification in encoded_task_specifications
            if encoded_task_specification[0].split(":")[1] == "task"
        ]

    @classmethod
    def _filenames_from_set(cls, filenames_set):
        files_str = (filenames_set.split("{", 1)[1]).rsplit("}", 1)[0]
        filenames = files_str.split(";")
        if filenames[0] == '':
            filenames = []
        return filenames

    @classmethod
    def _decode_task_specification(
        cls, encoded_task_specification, specification_file_directory
    ):
        task_name = encoded_task_specification[1]
        preconditions = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_task_specification[2]), specification_file_directory
        )
        posconditions = cls._smt2_properties_from_files(
            cls._filenames_from_set(encoded_task_specification[3]), specification_file_directory
        )

        return TaskSpecification(
            task_name, preconditions=preconditions, posconditions=posconditions
        )

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
                spec = spec+line
            file.close()
            s = (frozenset(spec_vars), spec, file_name)
        return s

    @classmethod
    def _smt2_properties_from_files(cls, file_names, specification_file_directory):
        properties = set()
        for file_name in file_names:
            properties.add(cls._smt2_property_from_file(file_name, specification_file_directory))
        return properties

    @classmethod
    def _dependencies_from_file(cls, encoded_specification):
        encoded_dependencies = encoded_specification[0].replace(" ", "")
        dependencies_as_text = encoded_dependencies.split("{", 1)[1].rsplit("}", 1)[0]
        nodes = dependencies_as_text.replace("(", "").replace(")", "").split(",")

        if nodes[0] == "":
            return set()

        return {
            (int(nodes[index]), int(nodes[index + 1]))
            for index in range(0, len(nodes), 2)
        }

    @classmethod
    def _checkpoint_properties_from_file(
        cls, encoded_specification, specification_file_directory
    ):
        encoded_checkpoints = encoded_specification[2:]
        encoded_checkpoints = [
            encoded_checkpoint.split(",") for encoded_checkpoint in encoded_checkpoints
        ]

        checkpoints = dict()
        for encoded_checkpoint in encoded_checkpoints:
            if encoded_checkpoint[0].split(":")[1] == "checkpoint":
                checkpoints[encoded_checkpoint[1]] = cls._decode_checkpoint_properties(
                    encoded_checkpoint, specification_file_directory
                )

        return checkpoints

    @classmethod
    def _decode_checkpoint_properties(
        cls, encoded_checkpoint, specification_file_directory
    ):
        return cls._smt2_properties_from_files(
                    cls._filenames_from_set(encoded_checkpoint[2]), specification_file_directory
               )

    def _graph_node_for_task_specification(self, task_specification):
        return self._graph.vs.find(task_specification=task_specification)

    def task_specification_named(self, task_name):
        # This method assumes there is a task named that way.
        return next(
            (task for task in self._task_specifications() if task.is_named(task_name))
        )

    def checkpoint_formulas_named(self, checkpoint_name):
        # This method assumes there is a task named that way.
        return self._checkpoint_properties[checkpoint_name]

    def _task_specifications(self):
        return self._graph.vs[self._task_specification_attribute_name()]

    def _build_workflow_graph(
        self, ordered_tasks, dependencies, start_node_index, end_node_index
    ):
        amount_of_tasks = len(ordered_tasks)
        list_of_edges = list(dependencies)

        self._graph = Graph(
            amount_of_tasks,
            list_of_edges,
            vertex_attrs={self._task_specification_attribute_name(): ordered_tasks},
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
        self._starting_task_specification = graph_start_node[
            self._task_specification_attribute_name()
        ]

    @staticmethod
    def _task_specification_attribute_name():
        return "task_specification"
