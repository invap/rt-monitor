# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import importlib.util
import logging
import os
import tomllib

from rt_monitor.errors.framework_errors import (
    FrameworkSpecificationError,
    ComponentsSpecificationError
)
from rt_monitor.errors.process_errors import ProcessSpecificationError
from rt_monitor.framework.components.component import VisualComponent, SelfLoggingComponent
from rt_monitor.framework.framework import Framework
from rt_monitor.framework.process.process_builder import ProcessBuilder


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
            f = open(framework_file, "rb")
        except FileNotFoundError:
            logging.error(f"Analysis framework specification file [ {framework_file} ] not found.")
            raise FrameworkSpecificationError()
        except PermissionError:
            logging.error(f"Permissions error opening file [ {framework_file} ].")
            raise FrameworkSpecificationError()
        except IsADirectoryError:
            logging.error(f"[ {framework_file} ] is a directory and not a file.")
            raise FrameworkSpecificationError()
        try:
            FrameworkBuilder.framework_dict = tomllib.load(f)
        except tomllib.TOMLDecodeError:
            logging.error(f"TOML decoding of file [ {framework_file} ] failed.")
            raise FrameworkSpecificationError()
        # Determining working directory
        if "working_directory" in FrameworkBuilder.framework_dict:
            FrameworkBuilder.files_path = FrameworkBuilder.framework_dict["working_directory"]
        else:
            FrameworkBuilder.files_path = FrameworkBuilder.spec_file_path

    @staticmethod
    def build_framework(override_visual):
        # Build analysis framework
        logging.info(f"Creating framework with file: {FrameworkBuilder.spec_file_name}.")
        # Building the process
        try:
            process = FrameworkBuilder._parse_process()
        except ProcessSpecificationError:
            logging.error(f"Process specification error.")
            raise FrameworkSpecificationError()
        # Building components structure
        try:
            components = FrameworkBuilder._parse_components(override_visual)
        except ComponentsSpecificationError:
            logging.error(f"Components definition error.")
            raise FrameworkSpecificationError()
        # Check that component variables appearing in the process are declared in the components
        for variable in process.variables():
            if (process.variables()[variable][0] == "Component" and
                    not any([variable in components[component].state() for component in components])):
                logging.error(f"Variable [ {variable} ] not declared in any component.")
                raise FrameworkSpecificationError()
        # There was no exception in building the framework.
        logging.info(f"Framework created.")
        return Framework(process, components)

    # Raises: ProcessSpecificationError()
    @staticmethod
    def _parse_process():
        if "process" not in FrameworkBuilder.framework_dict:
            logging.error(f"Process specification not found.")
            raise ProcessSpecificationError()
        process_dict = FrameworkBuilder.framework_dict["process"]
        return ProcessBuilder.build_process(process_dict, FrameworkBuilder.files_path)

    # Raises: ComponentError()
    @staticmethod
    def _parse_components(override_visual):
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
                    logging.error(f"Component file attribute missing in component [ {device_name} ] specification.")
                    raise ComponentsSpecificationError()
                component_path = absolute_component_path + "/" + component_file
                component_name = component_file.split(".")[0]
                # Load module specification from component name and path.
                try:
                    spec = importlib.util.spec_from_file_location(component_name, component_path)
                except (TypeError, ValueError) as e:
                    logging.critical(f"Loading component [ {component_name} ] form [ {component_path} ] error: {str(e)}.")
                    raise ComponentsSpecificationError()
                if spec is None:
                    logging.error(
                        f"Could not create module specification for [ {component_name} ] from file [ {component_path} ].")
                    raise ComponentsSpecificationError()
                # Load module from specification if the specification was correctly loaded
                try:
                    component_module = importlib.util.module_from_spec(spec)
                except AttributeError:
                    logging.error(f"Loader attribute for component [ {device_name} ] not found.")
                    raise ComponentsSpecificationError()
                except TypeError:
                    logging.error(f"Invalid module for component [ {device_name} ].")
                    raise ComponentsSpecificationError()
                # Load the module for component
                try:
                    spec.loader.exec_module(component_module)
                except (SyntaxError, AttributeError, NameError, TypeError, ValueError):
                    logging.error(f"The module for component [ {device_name} ] contains invalid python syntax.")
                    raise ComponentsSpecificationError()
                except ModuleNotFoundError:
                    logging.error(f"Module for component [ {device_name} ] not found.")
                    raise ComponentsSpecificationError()
                except ImportError:
                    logging.error(f"Error importing module for component [ {device_name} ].")
                    raise ComponentsSpecificationError()
                except FileNotFoundError:
                    logging.error(f"File not found for component [ {device_name} ].")
                    raise ComponentsSpecificationError()
                except PermissionError:
                    logging.error(f"Permission error opening file for component [ {device_name} ].")
                    raise ComponentsSpecificationError()
                try:
                    class_name = component["component_name"]
                except KeyError:
                    logging.error(f"Component name attribute missing in component [ {device_name} ] specification.")
                    raise ComponentsSpecificationError()
                # Obtain the class from the module
                try:
                    component_class = getattr(component_module, class_name)
                except AttributeError:
                    logging.error(
                        f"Component class [ {class_name} ] not found in module [ {component_name} ].")
                    raise ComponentsSpecificationError()
                # Component class was correctly loaded
                # Check whether visual capability has been overridden, whether it should be used according
                # to the global visual attribute and whether the components own visual attribute is set or not.
                # Note: if there is no global visual attribute, visual capability is blocked.
                if issubclass(component_class, VisualComponent):
                    if ("visual_component_file" not in component or
                            "visual_component_name" not in component):
                        logging.error(f"Visual component for component [ {component_name} ] missing.")
                        raise ComponentsSpecificationError()
                    # Information is present so, determine full class path for visual component
                    if "visual_component_path" in component:
                        absolute_visual_component_path = os.path.abspath(component["visual_component_path"])
                    else:
                        absolute_visual_component_path = absolute_general_components_path
                    visual_component_path = absolute_visual_component_path + "/" + component[
                        "visual_component_file"]
                    visual_component_name = component["visual_component_file"].split(".")[0]
                    # Load module specification from visual component name and path.
                    try:
                        spec = importlib.util.spec_from_file_location(visual_component_name, visual_component_path)
                    except (TypeError, ValueError) as e:
                        logging.critical(
                            f"Loading component [ {visual_component_name} ] form [ {visual_component_path} ] error: {str(e)}.")
                        raise ComponentsSpecificationError()
                    if spec is None:
                        logging.error(
                            f"Could not create module specification for component [ {visual_component_name} ] from file [ {visual_component_path} ].")
                        raise ComponentsSpecificationError()
                    # Load module from specification if the specification was correctly loaded
                    try:
                        visual_component_module = importlib.util.module_from_spec(spec)
                    except AttributeError:
                        logging.error(f"Loader attribute for visual component [ {visual_component_name} ] not found.")
                        raise ComponentsSpecificationError()
                    except TypeError:
                        logging.error(f"Invalid module for visual component [ {visual_component_name} ].")
                        raise ComponentsSpecificationError()
                    # Execution of the module for component
                    try:
                        spec.loader.exec_module(visual_component_module)
                    except (SyntaxError, AttributeError, NameError, TypeError, ValueError):
                        logging.error(f"The module for component [ {visual_component_name} ] contains invalid python syntax.")
                        raise ComponentsSpecificationError()
                    except ModuleNotFoundError:
                        logging.error(f"Module for component [ {visual_component_name} ] not found.")
                        raise ComponentsSpecificationError()
                    except ImportError:
                        logging.error(f"Error importing module for component [ {visual_component_name} ].")
                        raise ComponentsSpecificationError()
                    except FileNotFoundError:
                        logging.error(f"File not found for component [ {visual_component_name} ].")
                        raise ComponentsSpecificationError()
                    except PermissionError:
                        logging.error(f"Permission error opening file for component [ {visual_component_name} ].")
                        raise ComponentsSpecificationError()
                    visual_component_class_name = component["visual_component_name"]
                    # Obtain the class from the module
                    try:
                        visual_component_class = getattr(visual_component_module, visual_component_class_name)
                    except AttributeError:
                        logging.error(
                            f"Visual component class [ {visual_component_class_name} ] not found in module [ {visual_component_name} ].")
                        raise ComponentsSpecificationError()
                    if ((not override_visual) and
                            ("visual" in FrameworkBuilder.framework_dict["components"] and
                             FrameworkBuilder.framework_dict["components"]["visual"] is True) and
                            ("visual" not in component or component["visual"] is True)):
                        # The component has visual features and all conditions tu use it are set.
                        component_map[device_name] = component_class(visual_component_class, True)
                    else:
                        # The component has visual features but either it is overridden globally (the tool is running
                        # in command line mode) or the components local condition is set to false.
                        component_map[device_name] = component_class(visual_component_class, False)
                else:
                    component_map[device_name] = component_class()
        return component_map
