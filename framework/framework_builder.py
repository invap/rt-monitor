# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import importlib
import logging
import toml
from igraph import Graph

from errors.framework_errors import (
    FrameworkSpecificationError,
    LocalCheckpointSpecificationError,
    TaskSpecificationError,
    GlobalCheckpointSpecificationError,
    ProcessSpecificationError,
    ComponentsSpecificationError, UnsupportedNodeType, PropertySpecificationError
)
from framework.components.component import VisualComponent
from framework.framework import Framework
from framework.process.py_property import PyProperty
from framework.process.smt2_property import SMT2Property
from framework.process.sympy_property import SymPyProperty
from framework.process.process_node.checkpoint import Checkpoint
from framework.process.process_node.operator import Operator
from framework.process.process_node.task import Task
from framework.process.process import Process


class FrameworkBuilder:
    spec_file_path = ""
    spec_file_name = ""
    files_path = ""
    framework_dict = {}

    def __init__(self, framework_file):
        if framework_file[0] == "/" or framework_file[0] == ".":
            # framework_file was given with absolute or relative path.
            split_framework_file = framework_file.rsplit("/", 1)
            if len(split_framework_file) == 2:
                FrameworkBuilder.spec_file_path = split_framework_file[0]
                FrameworkBuilder.spec_file_name = split_framework_file[1]
            else:
                FrameworkBuilder.spec_file_path = "/"
                FrameworkBuilder.spec_file_name = split_framework_file[0]
        else:
            # framework_file was given as just a file name.
            FrameworkBuilder.spec_file_path = "process/"
            FrameworkBuilder.spec_file_name = framework_file
        # Parse TOML file and build dictionary
        try:
            FrameworkBuilder.framework_dict = toml.load(framework_file)
        except FileNotFoundError:
            logging.error(f"Framework file [ {FrameworkBuilder.spec_file_name} ] not found.")
            raise FrameworkSpecificationError()
        except toml.TomlDecodeError as e:
            logging.error(
                f"TOML decoding of file [ {FrameworkBuilder.spec_file_name} ] failed in [ line {e.lineno}, column {e.colno} ].")
            raise FrameworkSpecificationError()
        except PermissionError:
            logging.error(
                f"Permissions error opening file [ {FrameworkBuilder.spec_file_name} ].")
            raise FrameworkSpecificationError()
        # Determining working directory
        if "working_directory" in FrameworkBuilder.framework_dict:
            FrameworkBuilder.files_path = FrameworkBuilder.framework_dict["working_directory"]
        else:
            FrameworkBuilder.files_path = FrameworkBuilder.spec_file_path

    @staticmethod
    def build_framework(visual_global):
        # Build analysis framework
        logging.info(f"Creating framework with file: {FrameworkBuilder.spec_file_name}.")
        # Building process
        try:
            process = FrameworkBuilder._parse_process()
        except ProcessSpecificationError:
            logging.error(f"Process specification error.")
            raise FrameworkSpecificationError()
        # Building components structure
        try:
            components = FrameworkBuilder._parse_components(visual_global)
        except ComponentsSpecificationError:
            logging.error(f"Components definition error.")
            raise FrameworkSpecificationError()
        # There was no exception in building the framework.
        logging.info(f"Framework created.")
        return Framework(process, components, visual_global)

    # Raises: ProcessSpecificationError()
    @staticmethod
    def _parse_process():
        if "process" not in FrameworkBuilder.framework_dict:
            logging.error(f"Process specification not found.")
            raise ProcessSpecificationError()
        process_dict = FrameworkBuilder.framework_dict["process"]
        # Building the process toml_tasks_list
        ordered_nodes = []
        if "format" not in process_dict:
            logging.error(f"Process format not found.")
            raise ProcessSpecificationError()
        match process_dict["format"]:
            case "regex":
                logging.error(f"Process specification as regular expression not implemented yet.")
                raise ProcessSpecificationError()
            case "graph":
                reverse_node_name_map = {}  # Build a reverse map between node numbers and node names
                for node_number in range(0, len(process_dict["structure"]["nodes"])):
                    node = process_dict["structure"]["nodes"][node_number]
                    if not isinstance(node, list) or len(node) != 2:
                        logging.error(f"The {node_number + 1} node in the list of nodes is not well formed. It should "
                                      f"be [ node type, node name ]")
                        raise ProcessSpecificationError()
                    node_name = process_dict["structure"]["nodes"][node_number][0]
                    node_type = process_dict["structure"]["nodes"][node_number][1]
                    reverse_node_name_map[node_name] = node_number
                    # In the case of operators the shape of node_type is 'operator:<operator type>'.
                    split_node_type = node_type.split(":", 1)
                    match split_node_type[0]:
                        case "operator":
                            try:
                                ordered_nodes.append(Operator.new_of_type(split_node_type[1]))
                                # For the time being we are ignoring the name of the operators because they
                                # are not being used.
                                #
                                # Important note: The fact that the names are not being use right now does not give
                                # you the right to be a prick with your fellow workers by using shitty names like
                                # "op42" or "composition16". Be nice to people surrounding you, do not be that
                                # person everybody hates.
                            except IndexError():
                                logging.error(f"The operator node [ {node_name} ] is not well formed. It should be "
                                              f"of shape 'operator:<operator type>'.")
                                raise ProcessSpecificationError()
                        case "task":
                            try:
                                decoded_task = FrameworkBuilder._decode_task(node_name, process_dict["tasks"])
                            except TaskSpecificationError:
                                logging.error(f"Error decoding task from process node [ {node_name} ].")
                                raise ProcessSpecificationError()
                            ordered_nodes.append(decoded_task)
                        case "checkpoint":
                            try:
                                global_checkpoint = FrameworkBuilder._decode_global_checkpoints(
                                    node_name,
                                    process_dict["checkpoints"]
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
            case _:
                logging.error(f"Process format unknown.")
                raise ProcessSpecificationError()
        dependencies = {(reverse_node_name_map[src], reverse_node_name_map[trg]) for [src, trg] in process_dict["structure"]["edges"]}
        amount_of_elements = len(ordered_nodes)
        graph = Graph(
            amount_of_elements,
            dependencies,
            vertex_attrs={"process_node": ordered_nodes},
            directed=True,
        )
        starting_element = graph.vs[reverse_node_name_map[process_dict["structure"]["start"]]]["process_node"]
        try:
            variables = _get_variables_from_nodes([ordered_nodes[node] for node in range(0, amount_of_elements) if
                                                   not isinstance(ordered_nodes[node], Operator)])
        except UnsupportedNodeType as e:
            logging.error(f"Type [ {e.node_type()} ] of process node [ {e.node_name()} ] unknown.")
            raise ProcessSpecificationError()
        except PropertySpecificationError:
            logging.error(f"Inconsistent variable declarations.")
            raise ProcessSpecificationError()
        else:
            return Process(graph, starting_element, variables)

    # Raises: ComponentError()
    @staticmethod
    def _parse_components(visual_global):
        if "components" not in FrameworkBuilder.framework_dict:
            component_map = {}
        else:
            component_dict = FrameworkBuilder.framework_dict["components"]
            component_map = {}
            for component in component_dict:
                device_name = component["name"]
                # Extract component class
                component_class_path = component["component"]
                split_component_class_path = component_class_path.rsplit(".", 1)
                try:
                    component_module = importlib.import_module(split_component_class_path[0])
                except ModuleNotFoundError:
                    logging.error(f"Module [ {split_component_class_path[0]} ] not found.")
                    raise ComponentsSpecificationError()
                except ImportError:
                    logging.error(f"Error importing module [ {split_component_class_path[0]} ].")
                    raise ComponentsSpecificationError()
                try:
                    component_class = getattr(component_module, split_component_class_path[1])
                except AttributeError:
                    logging.error(
                        f"Component class [ {split_component_class_path[1]} ] not found in module [ {split_component_class_path[0]} ].")
                    raise ComponentsSpecificationError()
                # Component class was correctly loaded
                # Check whether component has visual features or not
                if issubclass(component_class, VisualComponent):
                    # The component has visual features
                    if "visual_component" in component:
                        # Extract component class
                        visual_component_class_path = component["visual_component"]
                        split_visual_component_class_path = visual_component_class_path.rsplit(".", 1)
                        try:
                            component_module = importlib.import_module(split_visual_component_class_path[0])
                        except ModuleNotFoundError:
                            logging.error(f"Module [ {split_visual_component_class_path[0]} ] not found.")
                            raise ComponentsSpecificationError()
                        except ImportError:
                            logging.error(f"Error importing module [ {split_visual_component_class_path[0]} ].")
                            raise ComponentsSpecificationError()
                        try:
                            visual_component_class = getattr(component_module, split_visual_component_class_path[1])
                        except AttributeError:
                            logging.error(f"Component class [ {split_visual_component_class_path[1]} ] not found in module [ {split_visual_component_class_path[0]} ].")
                            raise ComponentsSpecificationError()
                        if visual_global:
                            # Determine whether the component will execute with the associated visual feature
                            try:
                                visual = component["visual"]
                            except KeyError:
                                component_map[device_name] = component_class(visual_component_class, False)
                            else:
                                component_map[device_name] = component_class(visual_component_class, visual)
                        else:
                            component_map[device_name] = component_class(visual_component_class, False)
                    else:
                        logging.error(f"Visual component specification for [ {device_name} ] missing.")
                        raise ComponentsSpecificationError()
                else:
                    component_map[device_name] = component_class()
        return component_map

    # Raises: TaskSpecificationError()
    @staticmethod
    def _decode_task(task_name, toml_tasks_list):
        preconditions_list = []
        found = False
        for i in range(0, len(toml_tasks_list)):
            if found:
                break
            if toml_tasks_list[i]["name"] == task_name:
                found = True
                preconditions_list = toml_tasks_list[i]["pres"] if "pres" in toml_tasks_list[i] else []
        try:
            preconditions = FrameworkBuilder._properties_from_list(preconditions_list)
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
            postconditions = FrameworkBuilder._properties_from_list(postconditions_list)
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
            local_checkpoints = FrameworkBuilder._decode_local_checkpoints(checkpoints_list)
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
    def _decode_global_checkpoints(checkpoint_name, toml_checkpoints_list):
        properties_list = []
        found = False
        for i in range(0, len(toml_checkpoints_list)):
            if found:
                break
            if toml_checkpoints_list[i]["name"] == checkpoint_name:
                found = True
                properties_list = toml_checkpoints_list[i]["properties"]
        try:
            properties_from_list = FrameworkBuilder._properties_from_list(properties_list)
        except PropertySpecificationError:
            logging.error(f"Error decoding global checkpoint [ {checkpoint_name} ].")
            raise GlobalCheckpointSpecificationError()
        return Checkpoint(checkpoint_name, properties_from_list)

    # Raises: LocalCheckpointSpecificationError()
    @staticmethod
    def _decode_local_checkpoints(checkpoints_list):
        checkpoints = set()
        if not checkpoints_list == [{}]:
            for checkpoint in checkpoints_list:
                if "name" not in checkpoint:
                    logging.error(f"Local checkpoint name missing.")
                    raise LocalCheckpointSpecificationError()
                if "properties" not in checkpoint:
                    logging.error(f"Properties of local checkpoint [ {checkpoint["name"]} ] missing.")
                    raise LocalCheckpointSpecificationError()
                try:
                    properties_from_list = FrameworkBuilder._properties_from_list(checkpoint["properties"])
                except PropertySpecificationError:
                    logging.error(f"Error decoding local checkpoint [ {checkpoint["name"]} ].")
                    raise LocalCheckpointSpecificationError()
                checkpoints.add(Checkpoint(checkpoint["name"], properties_from_list))
        return checkpoints

    # Propagates: PropertySpecificationError()
    @staticmethod
    def _properties_from_list(properties_list):
        properties = set()
        if not properties_list == [{}]:
            for prop in properties_list:
                if "name" not in prop:
                    logging.error(f"Property name not found.")
                    raise PropertySpecificationError()
                if "file" not in prop and not ("formula" in prop and "variables" in prop):
                    logging.error(f"Property [ {prop["name"]} ] source unknown not found.")
                    raise PropertySpecificationError()
                if "formula" in prop:  # and "variables" in prop
                    # This operation might raise a PropertySpecificationError exception.
                    properties.add(_property_from_str(prop["name"], prop["format"], prop["variables"],
                                                      prop["formula"]))
                else:  # "file" in prop
                    file_name = prop["file"] if prop["file"][0] == "/" or prop["file"][0] == "." else FrameworkBuilder.files_path + "/" + prop["file"]
                    # This operation might raise a PropertySpecificationError exception.
                    properties.add(_property_from_file(prop["name"], prop["format"], file_name))
        return properties


# Raises: PropertySpecificationError()
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
                raise PropertySpecificationError()
    except FileNotFoundError:
        logging.error(f"File [ {file_name} ] for property [ {property_name} ] not found.")
        raise PropertySpecificationError()


# Raises: PropertySpecificationError()
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
            raise PropertySpecificationError()


# Raises: UnsupportedNodeType(), PropertySpecificationError()
def _get_variables_from_nodes(nodes):
    variables = {}
    for node in nodes:
        if isinstance(node, Task):
            for formula in node.preconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise PropertySpecificationError()
                    variables[variable] = formula.variables()[variable]
            for formula in node.postconditions():
                for variable in formula.variables():
                    if variable in variables and not variables[variable] == formula.variables()[variable]:
                        logging.error(
                            f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                        raise PropertySpecificationError()
                    variables[variable] = formula.variables()[variable]
            for checkpoint in node.checkpoints():
                for formula in checkpoint.properties():
                    for variable in formula.variables():
                        if variable in variables and not variables[variable] == formula.variables()[variable]:
                            logging.error(
                                f"Inconsistent declaration for variable [ {variable} ] - [ {variables[variable]} != {formula.variables()[variable]} ].")
                            raise PropertySpecificationError()
                        variables[variable] = formula.variables()[variable]
        elif isinstance(node, Checkpoint):
            for formula in node.properties():
                variables.update(formula.variables())
        else:
            raise UnsupportedNodeType(node.name(), node.type())
    return variables
