# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import importlib
import logging

import toml
from igraph import Graph
from toml import TomlDecodeError

from process_rt_monitor.errors import AbortRun
from process_rt_monitor.process.py_property import PyProperty
from process_rt_monitor.process.smt2_property import SMT2Property
from process_rt_monitor.process.sympy_property import SymPyProperty
from process_rt_monitor.process.process_errors import UnsupportedNodeType
from process_rt_monitor.process.process_node.checkpoint import Checkpoint
from process_rt_monitor.process.process_node.operator import Operator
from process_rt_monitor.process.process_node.task import Task
from process_rt_monitor.process.process import ProcessSpecification


class Framework:
    def __init__(self, file):
        self._file_path = file.rsplit("/", 1)[0]
        self._file_name = file.rsplit("/", 1)[1]
        try:
            self._toml_dict = toml.load(self._file_path + "/" + self._file_name)
        except TypeError as e:
            logging.error(f"Unsupported file type [ {self._file_name} ].")
            raise AbortRun()
        except TomlDecodeError as e:
            logging.error(
                f"TOML decoding of file [ {self._file_name} ] failed in [ line {e.lineno}, column {e.colno} ].")
            raise AbortRun()
        self._components = self._parse_components()
        self._process = self._parse_process()

    def components(self):
        return self._components

    def process(self):
        return self._process

    def _parse_components(self):
        if "components" not in self._toml_dict:
            component_map = {}
        else:
            component_dict = self._toml_dict["components"]
            component_map = {}
            for component in component_dict:
                device_name = component["name"]
                component_class_path = component["component"]
                split_component_class_path = component_class_path.rsplit(".", 1)
                component_module = importlib.import_module(split_component_class_path[0])
                component_class = getattr(component_module, split_component_class_path[1])
                component_map[device_name] = component_class()
        return component_map

    def _parse_process(self):
        if "process" not in self._toml_dict:
            logging.error(f"process missing in file [ {self._file_name} ].")
            raise AbortRun()
        process_dict = self._toml_dict["process"]
        # Building the process toml_tasks_list
        ordered_nodes = []
        if not "format" in process_dict:
            logging.error(f"process format undeclared in file [ {self._file_name} ].")
            raise AbortRun()
        match process_dict["format"]:
            case "regex":
                pass
            case "graph":
                for node_number in range(0, process_dict["structure"]["nodes"]):
                    node_type, node_name = process_dict["structure"]["map"][node_number][0], \
                        process_dict["structure"]["map"][node_number][1]
                    match node_type:
                        case "operator":
                            ordered_nodes.append(Operator.new_of_type(node_name))
                        case "task":
                            ordered_nodes.append(self._decode_task_specification(node_name, process_dict["tasks"]))
                        case "checkpoint":
                            ordered_nodes.append(
                                self._decode_global_checkpoints(node_name, process_dict["checkpoints"]))
                        case _:
                            logging.error(f"Type [ {node_type} ] of process node [ {node_name} ] unknown.")
                            raise AbortRun()
            case _:
                logging.error(f"Analysis framework format in file [ {self._file_name} ] unknown.")
                raise AbortRun()
        dependencies = {(src, trg) for [src, trg] in process_dict["structure"]["edges"]}
        amount_of_elements = len(ordered_nodes)
        graph = Graph(
            amount_of_elements,
            dependencies,
            vertex_attrs={"process_node": ordered_nodes},
            directed=True,
        )
        starting_element = graph.vs[process_dict["structure"]["start"]]["process_node"]
        variables = _get_variables_from_nodes([ordered_nodes[node] for node in range(0, amount_of_elements) if
                                               not isinstance(ordered_nodes[node], Operator)])
        return ProcessSpecification(graph, starting_element, variables)

    def _decode_task_specification(self, task_name, toml_tasks_list):
        preconditions_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name:
                found = True
                preconditions_list = toml_tasks_list[i]["pres"] if "pres" in toml_tasks_list[i] else []
        preconditions = self._properties_from_list(task_name, preconditions_list)
        postconditions_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name and "posts" in toml_tasks_list[i]:
                found = True
                postconditions_list = toml_tasks_list[i]["posts"] if "posts" in toml_tasks_list[i] else []
        postconditions = self._properties_from_list(task_name, postconditions_list)
        checkpoints_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name:
                found = True
                checkpoints_list = toml_tasks_list[i]["checkpoints"] if "checkpoints" in toml_tasks_list[i] else []
        local_checkpoints = self._decode_local_checkpoints(task_name, checkpoints_list)
        return Task(
            task_name,
            preconditions=preconditions,
            postconditions=postconditions,
            checkpoints=local_checkpoints,
        )

    def _decode_global_checkpoints(self, checkpoint_name, toml_checkpoints_list):
        properties_list = []
        found = False
        for i in range(0, len(toml_checkpoints_list)):
            if found:
                break
            if toml_checkpoints_list[i]["name"] == checkpoint_name:
                found = True
                properties_list = toml_checkpoints_list[i]["properties"]
        return Checkpoint(checkpoint_name, self._properties_from_list(checkpoint_name, properties_list))

    def _decode_local_checkpoints(self, task_name, checkpoints_list):
        checkpoints = set()
        if not checkpoints_list == [{}]:
            for checkpoint in checkpoints_list:
                if not "name" in checkpoint or not "properties" in checkpoint:
                    logging.critical(f"Checkpoint list [ {checkpoints_list} ] for task [ {task_name} ] malformed.")
                    raise AbortRun()
                checkpoints.add(Checkpoint(checkpoint["name"],
                                           self._properties_from_list(checkpoint["name"], checkpoint["properties"])))
        return checkpoints

    def _properties_from_list(self, name, properties_list):
        properties = set()
        if not properties_list == [{}]:
            for property in properties_list:
                if "file" not in property and not ("formula" in property and "variables" in property):
                    logging.critical(f"Property source unknown in [ {properties_list} ] of node [ {name} ].")
                    raise AbortRun()
                if "formula" in property:  # and "variables" in property
                    properties.add(_property_from_str(property["name"], property["format"], property["variables"],
                                                      property["formula"]))
                else:  # "file" in property
                    file_name = property["file"] if (
                            property["file"][0] == "." or property["file"][0] == "/") else self._file_path + "/" + \
                                                                                           property["file"]
                    properties.add(_property_from_file(property["name"], property["format"], file_name))
        return properties


def _property_from_file(property_name, property_format, file_name):
    try:
        match property_format:
            case "protosmt2":
                return SMT2Property.property_from_file(property_name, file_name)
            case "protosympy":
                return SymPyProperty.property_from_file(property_name, file_name)
            case "protopy":
                return PyProperty.property_from_file(property_name, file_name)
            case _:
                logging.error(f"Property format [ {property_format} ] unknown.")
                raise AbortRun()
    except FileNotFoundError as e:
        logging.error(f"File [ {e.filename()} ] does not exists.")
        raise AbortRun()


def _property_from_str(property_name, property_format, property_variables, property_formula):
    match property_format:
        case "protosmt2":
            return SMT2Property.property_from_str(property_name, property_variables, property_formula)
        case "protosympy":
            return SymPyProperty.property_from_str(property_name, property_variables, property_formula)
        case "protopy":
            return PyProperty.property_from_str(property_name, property_variables, property_formula)
        case _:
            logging.error(f"Property format [ {property_format} ] unknown.")
            raise AbortRun()


def _get_variables_from_nodes(nodes):
    variables = {}
    for node in nodes:
        if isinstance(node, Task):
            for formula in node.preconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise AbortRun()
                    variables[variable] = formula.variables()[variable]
            for formula in node.postconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise AbortRun()
                    variables[variable] = formula.variables()[variable]
            for checkpoint in node.checkpoints():
                for formula in checkpoint.properties():
                    for variable in formula.variables():
                        if variable in variables and not variables[variable] == formula.variables()[variable]:
                            logging.error(
                                f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                            raise AbortRun()
                        variables[variable] = formula.variables()[variable]
        elif isinstance(node, Checkpoint):
            for formula in node.properties():
                variables.update(formula.variables())
        else:
            raise UnsupportedNodeType(node.__class__)
    return variables
