# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import tomllib
import importlib
import os
import logging
# Create a logger for the monitor component
logger = logging.getLogger(__name__)

from rt_monitor.errors.framework_errors import FrameworkSpecificationError
from rt_monitor.errors.process_errors import ProcessSpecificationError
from rt_monitor.errors.component_errors import ComponentsSpecificationError
from rt_monitor.framework.process.process import Process
from rt_monitor.framework.process.graph_process import GraphProcess
from rt_monitor.framework.process.regex_process import RegExProcess


class Framework:
    def __init__(self, process, components):
        self._process = process
        self._components = components

    @staticmethod
    def framework_from_file(working_path, spec_filename):
        # Build analysis framework
        spec_complete_filename = working_path + spec_filename
        try:
            f = open(spec_complete_filename, "rb")
        except FileNotFoundError:
            logger.error(f"Framework file [ {spec_complete_filename} ] not found.")
            raise FrameworkSpecificationError()
        except PermissionError:
            logger.error(f"Permissions error opening file [ {spec_complete_filename} ].")
            raise FrameworkSpecificationError()
        except IsADirectoryError:
            logger.error(f"[ {spec_complete_filename} ] is a directory and not a file.")
            raise FrameworkSpecificationError()
        try:
            framework_dict = tomllib.load(f)
        except tomllib.TOMLDecodeError:
            logger.error(f"TOML decoding of file [ {spec_complete_filename} ] failed.")
            raise FrameworkSpecificationError()
        return Framework.framework_from_dict(framework_dict, working_path)

    @staticmethod
    def framework_from_dict(framework_dict, working_path):
        # Building the process
        try:
            process = Framework._parse_process(framework_dict['process'], working_path)
        except KeyError:
            logger.error(f"Process specification not found.")
            raise FrameworkSpecificationError()
        except ProcessSpecificationError:
            logger.error(f"Process specification error.")
            raise FrameworkSpecificationError()
        # Building components structure
        if "components" in framework_dict: 
            try:
                components = Framework._parse_components(framework_dict['components'])
            except ComponentsSpecificationError:
                logger.error(f"Components definition error.")
                raise FrameworkSpecificationError()
            # Check that component variables appearing in the process are declared in the components
            for variable in process.variables():
                if (process.variables()[variable][0] == "Component" and
                        not any([variable in components[component].state() for component in components])):
                    logger.error(f"Variable [ {variable} ] not declared in any component.")
                    raise FrameworkSpecificationError()
        else:
            components = {}
            if any([process.variables()[variable][0] == "Component" for variable in process.variables()]):
                logger.error(f"Process contains component variables but no components were defined.")
                raise FrameworkSpecificationError()
        # There was no exception in building the framework.
        logger.info(f"Framework created.")
        return Framework(process, components)

    def components(self):
        return self._components

    def process(self):
        return self._process

    # Raises: ProcessSpecificationError()
    @staticmethod
    def _parse_process(process_dict, working_path):
        if "format" not in process_dict:
            logger.error(f"Process format not found.")
            raise ProcessSpecificationError()
        factory = {
            "graph": GraphProcess,
            "regex": RegExProcess
        }
        process_type = process_dict["format"]
        if process_type not in factory:
            raise ProcessSpecificationError
        return factory[process_type].process_from_toml_dict(process_dict, working_path)

    # Raises: ComponentError()
    @staticmethod
    def _parse_components(component_dict):
        # Determine general path for components
        general_components_path = ""
        if "location" in component_dict:
            general_components_path = component_dict["location"]
        absolute_general_components_path = os.path.abspath(general_components_path)
        component_dict = component_dict["list"]
        component_map = {}
        for component in component_dict:
            device_name = component["name"]
            # Determine full class path for component
            if "component_path" in component:
                absolute_component_path = os.path.abspath(component["component_path"])
            else:
                absolute_component_path = absolute_general_components_path
            try:
                component_file = component["component_file"]
            except KeyError:
                logger.error(f"Component file attribute missing in component [ {device_name} ] specification.")
                raise ComponentsSpecificationError()
            component_path = absolute_component_path + "/" + component_file
            component_name = component_file.split(".")[0]
            # Load module specification from component name and path.
            try:
                spec = importlib.util.spec_from_file_location(component_name, component_path)
            except (TypeError, ValueError) as e:
                logger.critical(f"Loading component [ {component_name} ] form [ {component_path} ] error: {str(e)}.")
                raise ComponentsSpecificationError()
            if spec is None:
                logger.error(
                    f"Could not create module specification for [ {component_name} ] from file [ {component_path} ].")
                raise ComponentsSpecificationError()
            # Load module from specification if the specification was correctly loaded
            try:
                component_module = importlib.util.module_from_spec(spec)
            except AttributeError:
                logger.error(f"Loader attribute for component [ {device_name} ] not found.")
                raise ComponentsSpecificationError()
            except TypeError:
                logger.error(f"Invalid module for component [ {device_name} ].")
                raise ComponentsSpecificationError()
            # Load the module for component
            try:
                spec.loader.exec_module(component_module)
            except (SyntaxError, AttributeError, NameError, TypeError, ValueError):
                logger.error(f"The module for component [ {device_name} ] contains invalid python syntax.")
                raise ComponentsSpecificationError()
            except ModuleNotFoundError:
                logger.error(f"Module for component [ {device_name} ] not found.")
                raise ComponentsSpecificationError()
            except ImportError:
                logger.error(f"Error importing module for component [ {device_name} ].")
                raise ComponentsSpecificationError()
            except FileNotFoundError:
                logger.error(f"File not found for component [ {device_name} ].")
                raise ComponentsSpecificationError()
            except PermissionError:
                logger.error(f"Permission error opening file for component [ {device_name} ].")
                raise ComponentsSpecificationError()
            try:
                class_name = component["component_name"]
            except KeyError:
                logger.error(f"Component name attribute missing in component [ {device_name} ] specification.")
                raise ComponentsSpecificationError()
            # Obtain the class from the module
            try:
                component_class = getattr(component_module, class_name)
            except AttributeError:
                logger.error(
                    f"Component class [ {class_name} ] not found in module [ {component_name} ].")
                raise ComponentsSpecificationError()
            # Component class was correctly loaded
            component_map[device_name] = component_class()
        return component_map
