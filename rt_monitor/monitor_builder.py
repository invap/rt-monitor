# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import toml

from framework.components.component import SelfLoggingComponent
from framework.framework_builder import FrameworkBuilder
from monitor import Monitor
from rt_monitor.errors.monitor_errors import (
    FrameworkError,
    EventLogListError,
    MonitorConstructionError
)
from rt_monitor.errors.framework_errors import FrameworkSpecificationError


class MonitorBuilder:
    framework_file = ""
    report_list_file = ""

    def __init__(self, framework_file, report_list_file):
        MonitorBuilder.framework_file = framework_file
        MonitorBuilder.report_list_file = report_list_file

    # Raises: FrameworkError(), EventLogListError(), MonitorConstructionError()
    @staticmethod
    def build_monitor(visual=True):
        logging.info(f"Creating monitor with files: [ {MonitorBuilder.framework_file} ] and [ {MonitorBuilder.report_list_file} ].")
        try:
            framework_builder = FrameworkBuilder(MonitorBuilder.framework_file)
            framework = framework_builder.build_framework(visual)
        except FrameworkSpecificationError:
            logging.error(f"Error creating framework.")
            raise FrameworkError()
        # Exception EventLogListError() is propagated
        try:
            reports_map = MonitorBuilder._build_reports_map()
        except EventLogListError:
            # Stop components after correctly building the framework but failing to build the Event Log map.
            framework.stop_components()
            raise EventLogListError()
        # Check that names of components and names of event reports coincide.
        for report_key in reports_map.keys():
            if (report_key != "main" and
                    not any(report_key == component_key for component_key in framework.components().keys())):
                logging.info(f"Missing component [ {report_key} ] in [ {MonitorBuilder.framework_file} ].")
                # Stop components after correctly building the framework but failing to build the Monitor.
                framework.stop_components()
                raise MonitorConstructionError()
        for component_key in framework.components().keys():
            if (isinstance(framework.components()[component_key], SelfLoggingComponent) and
                    not any(component_key == report_key for report_key in reports_map.keys())):
                logging.info(f"Missing event report for component [ {component_key} ] in [ {MonitorBuilder.report_list_file} ].")
                # Stop components after correctly building the framework but failing to build the Monitor.
                framework.stop_components()
                raise MonitorConstructionError()
        # Build monitor
        logging.info(f"Creating monitor...")
        monitor = Monitor(framework, reports_map)
        logging.info(f"Monitor created.")
        return monitor

    @staticmethod
    def _build_reports_map():
        # Build report list map
        reports_map = {}
        logging.info(f"Loading event report list from file: {MonitorBuilder.report_list_file}...")
        try:
            toml_reports_map = toml.load(MonitorBuilder.report_list_file)
        except FileNotFoundError:
            logging.error(f"Event report list file [ {MonitorBuilder.report_list_file} ] not found.")
            raise EventLogListError()
        except toml.TomlDecodeError as e:
            logging.error(f"TOML decoding of file [ {MonitorBuilder.report_list_file} ] failed in [ line {e.lineno}, column {e.colno} ].")
            raise EventLogListError()
        except PermissionError:
            logging.error(f"Permissions error opening file [ {MonitorBuilder.report_list_file} ].")
            raise EventLogListError()
        if len(toml_reports_map.keys()) > 1 or "event_reports" not in toml_reports_map:
            logging.error(f"Event report list file format error.")
            raise EventLogListError()
        for event_report in toml_reports_map["event_reports"]:
            report_name = event_report["name"]
            report_filename = event_report["file"]
            logging.info(f"\tLoading event report for component [ {report_name} ] from file [ {report_filename} ].")
            try:
                reports_map[report_name] = open(report_filename, "r")
            except FileNotFoundError:
                logging.error(f"Event report file [ {report_filename} ] not found.")
                raise EventLogListError()
        if "main" not in reports_map:
            logging.error(f"Main event report file not found.")
            raise EventLogListError()
        # There was no problem building the event log map.
        logging.info(f"Event report list loaded")
        return reports_map

