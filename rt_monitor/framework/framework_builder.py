# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import importlib.util
import os
import logging
# Create a logger for the framework builder component
logger = logging.getLogger(__name__)

from rt_monitor.errors.framework_errors import (
    FrameworkSpecificationError,
    ComponentsSpecificationError
)
from rt_monitor.errors.process_errors import ProcessSpecificationError
from rt_monitor.framework.framework import Framework
from rt_monitor.framework.process.process_builder import ProcessBuilder


class FrameworkBuilder:
    files_path = ""
    framework_dict = {}

    def __init__(self, framework_dict):
        FrameworkBuilder.framework_dict = framework_dict
        # Determining working directory
        if "working_directory" in FrameworkBuilder.framework_dict:
            FrameworkBuilder.files_path = FrameworkBuilder.framework_dict["working_directory"]
        else:
            FrameworkBuilder.files_path = "./"

    @staticmethod
    def build_framework():
        # Build analysis framework
        # Building the process
        try:
            process = FrameworkBuilder._parse_process()
        except ProcessSpecificationError:
            logger.error(f"Process specification error.")
            raise FrameworkSpecificationError()
        # Building components structure
        try:
            components = FrameworkBuilder._parse_components()
        except ComponentsSpecificationError:
            logger.error(f"Components definition error.")
            raise FrameworkSpecificationError()
        # Check that component variables appearing in the process are declared in the components
        for variable in process.variables():
            if (process.variables()[variable][0] == "Component" and
                    not any([variable in components[component].state() for component in components])):
                logger.error(f"Variable [ {variable} ] not declared in any component.")
                raise FrameworkSpecificationError()
        # There was no exception in building the framework.
        logger.info(f"Framework created.")
        return Framework(process, components)

    # Raises: ProcessSpecificationError()
    @staticmethod
    def _parse_process():
        if "process" not in FrameworkBuilder.framework_dict:
            logger.error(f"Process specification not found.")
            raise ProcessSpecificationError()
        process_dict = FrameworkBuilder.framework_dict["process"]
        return ProcessBuilder.build_process(process_dict, FrameworkBuilder.files_path)

    # Raises: ComponentError()
    @staticmethod
    def _parse_components():
        if "components" not in FrameworkBuilder.framework_dict:
            component_map = {}
        else:
            # Determine general path for components
            general_components_path = ""
            if "location" in FrameworkBuilder.framework_dict["components"]:
                general_components_path = FrameworkBuilder.framework_dict["components"]["location"]
            absolute_general_components_path = os.path.abspath(general_components_path)
            component_dict = FrameworkBuilder.framework_dict["components"]["list"]
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
